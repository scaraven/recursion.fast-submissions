//! The client of the v4 oracle service (`service/PROTOCOL.md`): `QUERY` batches, `SIGN`, `VK` over
//! the Unix socket named by `RF_ORACLE`. One connection per prover thread (a pool: a thread takes
//! a connection for a whole batch and returns it), at most `MAX_CONNS` open. Every error (a refusal,
//! a closed connection) aborts the process with the service's message: a refused call has no
//! answers, so the proof cannot be made.

use std::fs::File;
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Condvar, Mutex};

use crate::blake2s::Digest;
use crate::format::Sig;
use crate::oracle::{Builder, Oracle};
use crate::par;

pub const OP_QUERY: u8 = 1;
pub const OP_SIGN: u8 = 2;
pub const OP_VK: u8 = 3;
/// The service's caps (PROTOCOL.md §3).
pub const BODY_CAP: usize = 1 << 24;
pub const QUERY_CAP: usize = 1 << 20;
pub const SIGN_ITEMS_CAP: usize = 1 << 16;
/// Connections this client opens at most (the service's cap is 64).
pub const MAX_CONNS: usize = 60;
/// A `QUERY` batch: at most this many items and about this many body bytes.
pub const BATCH_ITEMS: usize = 4096;
pub const BATCH_BYTES: usize = 4 << 20;

/// Print the error and exit with status 3.
pub fn fatal(msg: &str) -> ! {
    eprintln!("spartan-srom-prover: oracle service: {msg}");
    std::process::exit(3)
}

struct Pool {
    idle: Vec<UnixStream>,
    open: usize,
}

pub struct Service {
    path: String,
    /// For a socket path too long for `sun_path` (108 bytes): its directory, held open, and the
    /// name, connected to as `/proc/self/fd/<fd>/<name>`.
    dir: Option<(File, String)>,
    pool: Mutex<Pool>,
    cv: Condvar,
    /// requests sent, queries sent (QUERY and SIGN), query bytes sent
    pub requests: AtomicU64,
    pub queries: AtomicU64,
    pub query_bytes: AtomicU64,
    pub signs: AtomicU64,
}

fn status_name(s: u8) -> &'static str {
    match s {
        1 => "BAD",
        2 => "CAP",
        3 => "EXHAUSTED",
        _ => "unknown status",
    }
}

fn open_stream(path: &str, dir: &Option<(File, String)>) -> std::io::Result<UnixStream> {
    match dir {
        None => UnixStream::connect(path),
        Some((d, name)) => UnixStream::connect(format!("/proc/self/fd/{}/{name}", d.as_raw_fd())),
    }
}

impl Service {
    /// Connect to the socket at `path` (one connection is opened now and kept for later use).
    pub fn connect(path: &str) -> Result<Service, String> {
        let dir = if path.len() >= 100 {
            let p = std::path::Path::new(path);
            let (parent, name) = (p.parent().ok_or("RF_ORACLE: no directory")?, p.file_name().ok_or("RF_ORACLE: no name")?);
            let d = File::open(parent).map_err(|e| format!("{}: {e}", parent.display()))?;
            Some((d, name.to_string_lossy().into_owned()))
        } else {
            None
        };
        let c = open_stream(path, &dir).map_err(|e| format!("connect {path}: {e}"))?;
        Ok(Service {
            path: path.to_string(),
            dir,
            pool: Mutex::new(Pool { idle: vec![c], open: 1 }),
            cv: Condvar::new(),
            requests: AtomicU64::new(0),
            queries: AtomicU64::new(0),
            query_bytes: AtomicU64::new(0),
            signs: AtomicU64::new(0),
        })
    }

    /// Open connections until `k` are idle (start-up, before the clock starts).
    pub fn warm(&self, k: usize) {
        let mut conns = vec![];
        for _ in 0..k.min(MAX_CONNS) {
            conns.push(self.take());
        }
        for c in conns {
            self.put(c);
        }
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
                return open_stream(&self.path, &self.dir).unwrap_or_else(|e| fatal(&format!("connect {}: {e}", self.path)));
            }
            p = self.cv.wait(p).unwrap();
        }
    }

    fn put(&self, c: UnixStream) {
        self.pool.lock().unwrap().idle.push(c);
        self.cv.notify_one();
    }

    /// Send `req` (a 16-byte header slot followed by the body) and return the response body.
    fn call(&self, conn: &mut UnixStream, op: u8, count: usize, req: &mut [u8]) -> Vec<u8> {
        let body_len = req.len() - 16;
        req[0] = op;
        req[1..4].fill(0);
        req[4..8].copy_from_slice(&(count as u32).to_le_bytes());
        req[8..16].copy_from_slice(&(body_len as u64).to_le_bytes());
        let what = match op {
            OP_QUERY => "QUERY",
            OP_SIGN => "SIGN",
            _ => "VK",
        };
        conn.write_all(req).unwrap_or_else(|e| fatal(&format!("{what} ({count} items, {body_len} bytes): write: {e}")));
        let mut hdr = [0u8; 16];
        conn.read_exact(&mut hdr)
            .unwrap_or_else(|e| fatal(&format!("{what} ({count} items, {body_len} bytes): read: {e}")));
        let n = u64::from_le_bytes(hdr[8..16].try_into().unwrap()) as usize;
        let mut body = vec![0u8; n];
        conn.read_exact(&mut body).unwrap_or_else(|e| fatal(&format!("{what}: read body: {e}")));
        self.requests.fetch_add(1, Ordering::Relaxed);
        if hdr[0] != 0 {
            fatal(&format!(
                "{what} ({count} items, {body_len} bytes) refused with status {} {}: {}",
                hdr[0],
                status_name(hdr[0]),
                String::from_utf8_lossy(&body)
            ));
        }
        body
    }

    fn push_item(req: &mut Vec<u8>, q: &[u8]) {
        req.extend_from_slice(&(q.len() as u32).to_le_bytes());
        req.extend_from_slice(q);
    }

    /// `SIGN` the queries: their answers (computed by the service) and the signature.
    pub fn sign(&self, qs: &[&[u8]]) -> (Vec<Digest>, Sig) {
        let mut req = vec![0u8; 16];
        let mut bytes = 0u64;
        for q in qs {
            Self::push_item(&mut req, q);
            bytes += q.len() as u64;
        }
        let mut conn = self.take();
        let body = self.call(&mut conn, OP_SIGN, qs.len(), &mut req);
        self.put(conn);
        self.signs.fetch_add(1, Ordering::Relaxed);
        self.queries.fetch_add(qs.len() as u64, Ordering::Relaxed);
        self.query_bytes.fetch_add(bytes, Ordering::Relaxed);
        let m = qs.len();
        if body.len() != 32 * m + 4772 {
            fatal(&format!("SIGN: response of {} bytes, expected {}", body.len(), 32 * m + 4772));
        }
        let ans: Vec<Digest> = (0..m).map(|i| body[32 * i..32 * i + 32].try_into().unwrap()).collect();
        let s = &body[32 * m..];
        let idx = u32::from_le_bytes(s[..4].try_into().unwrap()) as u64;
        let d = |k: usize| -> Digest { s[4 + 32 * k..36 + 32 * k].try_into().unwrap() };
        let sig = Sig { idx, ots: (0..133).map(d).collect(), path: (133..149).map(d).collect() };
        (ans, sig)
    }

    /// The service's public key.
    pub fn vk(&self) -> Digest {
        let mut conn = self.take();
        let mut req = vec![0u8; 16];
        let body = self.call(&mut conn, OP_VK, 0, &mut req);
        self.put(conn);
        body.as_slice().try_into().unwrap_or_else(|_| fatal("VK: not 32 bytes"))
    }

    pub fn report(&self) -> String {
        let g = |x: &AtomicU64| x.load(Ordering::Relaxed);
        format!(
            "service_requests={} service_queries={} service_query_bytes={} service_signs={} connections={}",
            g(&self.requests),
            g(&self.queries),
            g(&self.query_bytes),
            g(&self.signs),
            self.pool.lock().unwrap().open
        )
    }
}

impl Oracle for Service {
    fn ask(&self, q: &[u8]) -> Digest {
        let mut req = Vec::with_capacity(20 + q.len());
        req.resize(16, 0);
        Self::push_item(&mut req, q);
        let mut conn = self.take();
        let body = self.call(&mut conn, OP_QUERY, 1, &mut req);
        self.put(conn);
        self.queries.fetch_add(1, Ordering::Relaxed);
        self.query_bytes.fetch_add(q.len() as u64, Ordering::Relaxed);
        body[..32].try_into().unwrap_or_else(|_| fatal("QUERY: short answer"))
    }

    fn ask_many(&self, out: &mut [Digest], build: &Builder) {
        par::for_each_chunk_mut(out, 256, |off, chunk| {
            let mut conn = self.take();
            let mut req: Vec<u8> = Vec::with_capacity(BATCH_BYTES + (1 << 16));
            let mut i = 0;
            while i < chunk.len() {
                req.clear();
                req.resize(16, 0);
                let start = i;
                let mut bytes = 0u64;
                while i < chunk.len() && i - start < BATCH_ITEMS && req.len() < BATCH_BYTES {
                    let lp = req.len();
                    req.extend_from_slice(&[0u8; 4]);
                    build(off + i, &mut req);
                    let len = req.len() - lp - 4;
                    if len > QUERY_CAP {
                        fatal(&format!("a query of {len} bytes is above the cap of {QUERY_CAP}"));
                    }
                    req[lp..lp + 4].copy_from_slice(&(len as u32).to_le_bytes());
                    bytes += len as u64;
                    i += 1;
                }
                if req.len() - 16 > BODY_CAP {
                    fatal(&format!("a QUERY body of {} bytes is above the cap of {BODY_CAP}", req.len() - 16));
                }
                let count = i - start;
                let body = self.call(&mut conn, OP_QUERY, count, &mut req);
                if body.len() != 32 * count {
                    fatal(&format!("QUERY: {} answer bytes for {count} queries", body.len()));
                }
                for (k, o) in chunk[start..i].iter_mut().enumerate() {
                    *o = body[32 * k..32 * k + 32].try_into().unwrap();
                }
                self.queries.fetch_add(count as u64, Ordering::Relaxed);
                self.query_bytes.fetch_add(bytes, Ordering::Relaxed);
            }
            self.put(conn);
        });
    }
}
