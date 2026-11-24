//! The client of the oracle service (`service/PROTOCOL.md`): `QUERY` batches, `SIGN`, `VK` over the Unix socket
//! named by `RF_ORACLE`. Adapted from season 1 (`archive/season-1/wide-packs/prover/src/service.rs`: framing, pool,
//! `fatal`, the SIGN response parser), with the v6 changes:
//! - **no connection before `go`**: `Service::connect` only records the path; the first connection is opened by
//!   the first request (the socket does not exist before `go`; PROVER.md §3). No `warm()`.
//! - `vk` comes from `/work/vk.hex` (the `VK` op stays for dev tools only).
//! - `SIGN` is one request at a time, waited for (`sign`): the service assigns one-time indices in completion
//!   order and a replay refuses any other order, so the order must be the inputs' (no `sign_during` overlap).
//! - writes use `write(2)` (`write_all`); `sendmsg` is refused in a request.
//! - the multi-connection pipelining and the per-class RTT logs of season 1 are left out (a later stage may port
//!   them back: they change speed, not bytes).
//!
//! Every error (a refusal, a closed connection) aborts the process with the service's message: a refused call
//! has no answers, so the proof cannot be made. No request is ever retried.

use std::fs::File;
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Condvar, Mutex};

use crate::format::Sig;
use crate::keccak::Digest;
use crate::oracle::{Builder, Oracle};

pub const OP_QUERY: u8 = 1;
pub const OP_SIGN: u8 = 2;
pub const OP_VK: u8 = 3;
/// The service's caps (PROTOCOL.md §3).
pub const BODY_CAP: usize = 1 << 24;
pub const QUERY_CAP: usize = 1 << 20;
pub const QUERY_ITEMS_CAP: usize = 1 << 18;
pub const SIGN_ITEMS_CAP: usize = 1 << 16;
/// Connections one client opens at most. A request holds two clients (the oracle's and the one that SIGNs, which
/// opens one connection), so 30 + 1 stays below the service's cap of 32.
pub const MAX_CONNS: usize = 30;
/// A `QUERY` batch: at most this many items and about this many body bytes (PROTOCOL.md §4: 256–4096 items).
pub const BATCH_ITEMS: usize = 4096;
pub const BATCH_BYTES: usize = 256 << 10;

/// The batch limits in use: `BATCH_ITEMS`/`BATCH_BYTES`, or `LVM6_BATCH_ITEMS` / `LVM6_BATCH_KIB` (measurement only:
/// a batch's answers do not depend on its size).
fn batch_limits() -> (usize, usize) {
    static L: std::sync::OnceLock<(usize, usize)> = std::sync::OnceLock::new();
    *L.get_or_init(|| {
        let env = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<usize>().ok());
        (
            env("LVM6_BATCH_ITEMS").map_or(BATCH_ITEMS, |v| v.clamp(1, QUERY_ITEMS_CAP)),
            env("LVM6_BATCH_KIB").map_or(BATCH_BYTES, |v| (v << 10).clamp(1 << 10, BODY_CAP >> 1)),
        )
    })
}

/// Print the error and exit with status 3.
pub fn fatal(msg: &str) -> ! {
    eprintln!("lvm6-prover: oracle service: {msg}");
    std::process::exit(3)
}

struct Pool {
    idle: Vec<UnixStream>,
    open: usize,
}

pub struct Service {
    path: String,
    /// For a socket path too long for `sun_path` (108 bytes): its directory, held open, and the name, connected
    /// to as `/proc/self/fd/<fd>/<name>` (local dev runs; in the sandbox the path is `/run/rf/oracle.sock`).
    dir: Option<(File, String)>,
    pool: Mutex<Pool>,
    cv: Condvar,
    pub requests: AtomicU64,
    pub signs: AtomicU64,
}

fn status_name(s: u8) -> &'static str {
    match s {
        1 => "BAD",
        2 => "CAP",
        3 => "EXHAUSTED",
        4 => "MISMATCH",
        _ => "unknown status",
    }
}

fn what(op: u8) -> &'static str {
    match op {
        OP_QUERY => "QUERY",
        OP_SIGN => "SIGN",
        _ => "VK",
    }
}

impl Service {
    /// The client of the socket at `path`. Opens nothing: call it after `go`, and the first request connects.
    pub fn connect(path: &str) -> Result<Service, String> {
        let dir = if path.len() >= 100 {
            let p = std::path::Path::new(path);
            let (parent, name) = (p.parent().ok_or("RF_ORACLE: no directory")?, p.file_name().ok_or("RF_ORACLE: no name")?);
            let d = File::open(parent).map_err(|e| format!("{}: {e}", parent.display()))?;
            Some((d, name.to_string_lossy().into_owned()))
        } else {
            None
        };
        Ok(Service {
            path: path.to_string(),
            dir,
            pool: Mutex::new(Pool { idle: vec![], open: 0 }),
            cv: Condvar::new(),
            requests: AtomicU64::new(0),
            signs: AtomicU64::new(0),
        })
    }

    fn open_stream(&self) -> UnixStream {
        let r = match &self.dir {
            None => UnixStream::connect(&self.path),
            Some((d, name)) => UnixStream::connect(format!("/proc/self/fd/{}/{name}", d.as_raw_fd())),
        };
        r.unwrap_or_else(|e| fatal(&format!("connect {}: {e}", self.path)))
    }

    fn take(&self) -> UnixStream {
        let mut p = self.pool.lock().unwrap();
        loop {
            if let Some(c) = p.idle.pop() {
                return c;
            }
            if p.open < MAX_CONNS {
                p.open += 1;
                drop(p);
                return self.open_stream();
            }
            p = self.cv.wait(p).unwrap();
        }
    }

    fn put(&self, c: UnixStream) {
        self.pool.lock().unwrap().idle.push(c);
        self.cv.notify_one();
    }

    /// Write the request `req` (a 16-byte header slot, filled here, then the body).
    fn send(conn: &mut UnixStream, op: u8, count: usize, req: &mut [u8]) {
        let body_len = req.len() - 16;
        req[0] = op;
        req[1..4].fill(0);
        req[4..8].copy_from_slice(&(count as u32).to_le_bytes());
        req[8..16].copy_from_slice(&(body_len as u64).to_le_bytes());
        conn.write_all(req)
            .unwrap_or_else(|e| fatal(&format!("{} ({count} items, {body_len} bytes): write: {e}", what(op))));
    }

    /// Read the response to a request sent with `send`; a non-zero status is fatal.
    fn recv(&self, conn: &mut UnixStream, op: u8, count: usize, body_len: usize) -> Vec<u8> {
        let mut hdr = [0u8; 16];
        conn.read_exact(&mut hdr)
            .unwrap_or_else(|e| fatal(&format!("{} ({count} items, {body_len} bytes): read: {e}", what(op))));
        let n = u64::from_le_bytes(hdr[8..16].try_into().unwrap()) as usize;
        let mut body = vec![0u8; n];
        conn.read_exact(&mut body).unwrap_or_else(|e| fatal(&format!("{}: read body: {e}", what(op))));
        self.requests.fetch_add(1, Ordering::Relaxed);
        if hdr[0] != 0 {
            fatal(&format!(
                "{} ({count} items, {body_len} bytes) refused with status {} {}: {}",
                what(op),
                hdr[0],
                status_name(hdr[0]),
                String::from_utf8_lossy(&body)
            ));
        }
        body
    }

    fn call(&self, op: u8, count: usize, req: &mut [u8]) -> Vec<u8> {
        let mut conn = self.take();
        Self::send(&mut conn, op, count, req);
        let body = self.recv(&mut conn, op, count, req.len() - 16);
        self.put(conn);
        body
    }

    fn push_item(req: &mut Vec<u8>, q: &[u8]) {
        if q.len() > QUERY_CAP {
            fatal(&format!("a query of {} bytes is above queryCap ({QUERY_CAP})", q.len()));
        }
        req.extend_from_slice(&(q.len() as u32).to_le_bytes());
        req.extend_from_slice(q);
    }

    /// `SIGN` the queries, one request, waited for: their answers (computed by the service) and the signature.
    pub fn sign(&self, qs: &[&[u8]]) -> (Vec<Digest>, Sig) {
        let mut req = vec![0u8; 16];
        for q in qs {
            Self::push_item(&mut req, q);
        }
        let m = qs.len();
        if req.len() - 16 > BODY_CAP || m > SIGN_ITEMS_CAP {
            fatal(&format!(
                "SIGN of {m} queries ({} body bytes) is above the service's caps ({SIGN_ITEMS_CAP} items, {BODY_CAP} bytes)",
                req.len() - 16
            ));
        }
        let body = self.call(OP_SIGN, m, &mut req);
        self.signs.fetch_add(1, Ordering::Relaxed);
        if body.len() != 32 * m + 4772 {
            fatal(&format!("SIGN: response of {} bytes, expected {}", body.len(), 32 * m + 4772));
        }
        let s = &body[32 * m..];
        let idx = u32::from_le_bytes(s[..4].try_into().unwrap()) as u64;
        let d = |k: usize| -> Digest { s[4 + 32 * k..36 + 32 * k].try_into().unwrap() };
        let sig = Sig { idx, ots: (0..133).map(d).collect(), path: (133..149).map(d).collect() };
        (body[..32 * m].chunks_exact(32).map(|a| a.try_into().unwrap()).collect(), sig)
    }

    /// The service's public key (dev tools; a request reads `/work/vk.hex`).
    pub fn vk(&self) -> Digest {
        let mut req = vec![0u8; 16];
        let body = self.call(OP_VK, 0, &mut req);
        body.as_slice().try_into().unwrap_or_else(|_| fatal("VK: not 32 bytes"))
    }

    /// `out[i] = H(q_i)` on one connection, in `QUERY` batches of at most `BATCH_ITEMS` items and about
    /// `BATCH_BYTES` body bytes, one request in flight.
    fn batches(&self, out: &mut [Digest], build: &Builder) {
        let n = out.len();
        let (batch_items, batch_bytes) = batch_limits();
        let mut conn = self.take();
        let mut req: Vec<u8> = Vec::with_capacity(batch_bytes + (1 << 16));
        let mut buf = Vec::new();
        let mut i = 0;
        while i < n {
            req.clear();
            req.resize(16, 0);
            let start = i;
            while i < n && i - start < batch_items && (i == start || req.len() - 16 < batch_bytes) {
                buf.clear();
                build(i, &mut buf);
                if req.len() - 16 + 4 + buf.len() > BODY_CAP && i > start {
                    break;
                }
                Self::push_item(&mut req, &buf);
                i += 1;
            }
            let count = i - start;
            Self::send(&mut conn, OP_QUERY, count, &mut req);
            let body = self.recv(&mut conn, OP_QUERY, count, req.len() - 16);
            if body.len() != 32 * count {
                fatal(&format!("QUERY: {} answer bytes for {count} queries", body.len()));
            }
            for (o, a) in out[start..i].iter_mut().zip(body.chunks_exact(32)) {
                *o = a.try_into().unwrap();
            }
        }
        self.put(conn);
    }
}

impl Oracle for Service {
    fn ask(&self, q: &[u8]) -> Digest {
        let mut out = [[0u8; 32]];
        self.batches(&mut out, &|_, buf: &mut Vec<u8>| buf.extend_from_slice(q));
        out[0]
    }
    fn ask_many_here(&self, out: &mut [Digest], build: &Builder) {
        self.batches(out, build);
    }
    fn name(&self) -> &'static str {
        "service"
    }
}
