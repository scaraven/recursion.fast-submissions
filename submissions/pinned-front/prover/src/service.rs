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

use crate::format::Sig;
use crate::keccak::Digest;
use crate::oracle::{Builder, Oracle};

pub const OP_QUERY: u8 = 1;
pub const OP_SIGN: u8 = 2;
pub const OP_VK: u8 = 3;
/// The service's caps (PROTOCOL.md §3).
pub const BODY_CAP: usize = 1 << 24;
pub const QUERY_CAP: usize = 1 << 20;
pub const SIGN_ITEMS_CAP: usize = 1 << 16;
/// Connections this client's pool opens at most. The service refuses a 33rd open connection
/// (PROTOCOL.md §1, cap 32) and `ask` keeps one more for the Fiat–Shamir queries, so the pool stays
/// at 31. Beyond about 16 there is no gain anyway, since the service computes on the same CPUs.
pub const MAX_CONNS: usize = 31;
/// Connections opened before `ready` (`warm`).
pub const WARM_CONNS: usize = 16;
/// A `QUERY` batch: at most this many items and about this many body bytes.
pub const BATCH_ITEMS: usize = 4096;
/// TRN: 256 KiB (P1's 4 MiB was never tuned): the service's request body then stays in its core's
/// L2 between its `read` and its hashing, and the client blocks less (TRN §3: −34 % of the leaf time).
pub const BATCH_BYTES: usize = 256 << 10;
/// R9-PCS: how many requests one hashing call (leaves or nodes) keeps in flight, one per connection, so the service
/// computes the next batch while the caller reads an answer and writes a request: `⌈CPUs / pool threads⌉`, at most 4.
/// - With a worker per CPU that is 1, the plain round trip: the hashing phases are then bound by the CPUs the service
///   and the encode share, and a second request per worker measured no faster or slower (dev, 8 threads on 8 CPUs).
/// - With fewer workers than CPUs, one connection a worker leaves CPUs idle that the service could hash on; the
///   extra requests fill them (dev, 4 threads on 8 CPUs: the `C_main` commit 0.47 → 0.31 s, open main 0.27 → 0.21).
/// `LVM_INFLIGHT=k` sets it (1..=4; measurement only: the answers do not depend on it). The pool threads with their
/// connections stay within the service's 32 (`MAX_CONNS`; `try_take` never waits for a further one).
pub fn in_flight() -> usize {
    static N: AtomicU64 = AtomicU64::new(0);
    match N.load(Ordering::Relaxed) {
        0 => {
            let k = std::env::var("LVM_INFLIGHT").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or_else(|| {
                let cpus = std::thread::available_parallelism().map_or(1, |n| n.get());
                cpus.div_ceil(crate::lv::parallel::num_threads().max(1))
            });
            let k = k.clamp(1, 4);
            N.store(k as u64, Ordering::Relaxed);
            k
        }
        k => k as usize,
    }
}
/// R9-PCS: the fewest items a batch is cut to so that a call fills its connections (below it, one round trip of
/// tens of µs outweighs the overlap).
pub const SPLIT_MIN: usize = 64;

/// NTM: the `QUERY` body target actually used by `batches_on`: `BATCH_BYTES` unless `LVM_BATCH_KIB`
/// or a bench (`set_batch_bytes`) says otherwise (measurement only; the answers do not depend on it).
static BATCH_B: AtomicU64 = AtomicU64::new(0);
pub fn batch_bytes() -> usize {
    match BATCH_B.load(Ordering::Relaxed) {
        0 => {
            let b = std::env::var("LVM_BATCH_KIB").ok().and_then(|v| v.parse::<usize>().ok()).map_or(BATCH_BYTES, |k| (k << 10).clamp(1 << 12, BODY_CAP >> 1));
            BATCH_B.store(b as u64, Ordering::Relaxed);
            b
        }
        b => b as usize,
    }
}
pub fn set_batch_bytes(b: usize) {
    BATCH_B.store(b.clamp(1 << 12, BODY_CAP >> 1) as u64, Ordering::Relaxed);
}

/// Print the error and exit with status 3.
pub fn fatal(msg: &str) -> ! {
    eprintln!("lvm-prover: oracle service: {msg}");
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
    /// the connection of the sequential queries (`ask`), non-blocking
    fs: Mutex<Option<UnixStream>>,
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
            fs: Mutex::new(None),
            requests: AtomicU64::new(0),
            queries: AtomicU64::new(0),
            query_bytes: AtomicU64::new(0),
            signs: AtomicU64::new(0),
        })
    }

    /// Open connections until `k · in_flight()` are idle (start-up, before the clock starts): `k` hashing threads,
    /// each with the connections a call of several batches keeps busy.
    pub fn warm(&self, k: usize) {
        let mut conns = vec![];
        for _ in 0..(in_flight() * k).min(MAX_CONNS) {
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

    /// R9-PCS: one more connection for a call that already holds one, if one is idle or may still be opened; `None`
    /// rather than waiting, so threads that each hold one never wait on each other.
    fn try_take(&self) -> Option<UnixStream> {
        let mut p = self.pool.lock().unwrap();
        if let Some(c) = p.idle.pop() {
            return Some(c);
        }
        if p.open >= MAX_CONNS {
            return None;
        }
        p.open += 1;
        drop(p);
        Some(open_stream(&self.path, &self.dir).unwrap_or_else(|e| fatal(&format!("connect {}: {e}", self.path))))
    }

    /// R9-PCS: the connections for a call of `items` hashes: `in_flight()` when it splits into batches of at least
    /// `SPLIT_MIN` items each, else one; fewer if the service's cap is reached.
    fn take_for(&self, items: usize) -> Vec<UnixStream> {
        let m = in_flight();
        let mut conns = vec![self.take()];
        if m > 1 && items >= m * SPLIT_MIN {
            conns.extend((1..m).filter_map(|_| self.try_take()));
        }
        conns
    }

    fn put_all(&self, conns: Vec<UnixStream>) {
        for c in conns {
            self.put(c);
        }
    }

    fn put(&self, c: UnixStream) {
        self.pool.lock().unwrap().idle.push(c);
        self.cv.notify_one();
    }

    /// Send `req` (a 16-byte header slot followed by the body) and return the response body.
    fn call(&self, conn: &mut UnixStream, op: u8, count: usize, req: &mut [u8]) -> Vec<u8> {
        Self::send(conn, op, count, req);
        self.recv(conn, op, count, req.len() - 16)
    }

    fn what(op: u8) -> &'static str {
        match op {
            OP_QUERY => "QUERY",
            OP_SIGN => "SIGN",
            _ => "VK",
        }
    }

    /// Write the request `req` (header slot filled here).
    fn send(conn: &mut UnixStream, op: u8, count: usize, req: &mut [u8]) {
        let body_len = req.len() - 16;
        req[0] = op;
        req[1..4].fill(0);
        req[4..8].copy_from_slice(&(count as u32).to_le_bytes());
        req[8..16].copy_from_slice(&(body_len as u64).to_le_bytes());
        let what = Self::what(op);
        conn.write_all(req).unwrap_or_else(|e| fatal(&format!("{what} ({count} items, {body_len} bytes): write: {e}")));
    }

    /// Read the response to a request sent with `send`.
    fn recv(&self, conn: &mut UnixStream, op: u8, count: usize, body_len: usize) -> Vec<u8> {
        let what = Self::what(op);
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
        let (a, s, ()) = self.sign_during(qs, || ());
        (a, s)
    }

    /// [`Self::sign`], running `during` while the service computes (P6B, OH-DES P4).
    pub fn sign_during<R>(&self, qs: &[&[u8]], during: impl FnOnce() -> R) -> (Vec<Digest>, Sig, R) {
        let mut req = vec![0u8; 16];
        for q in qs {
            Self::push_item(&mut req, q);
        }
        let conn = self.sign_start(&mut req, qs.len());
        let r = during();
        let (body, sig) = self.sign_finish(conn, qs.len(), req.len() - 16);
        (body.chunks_exact(32).map(|a| a.try_into().unwrap()).collect(), sig, r)
    }

    /// Send a `SIGN` of the `count` items in `req[16..]` (each `len:u32 ‖ q`), without waiting for
    /// the answer (`sign_finish`), so the caller can work while the service hashes.
    pub fn sign_start(&self, req: &mut [u8], count: usize) -> UnixStream {
        // the service would refuse these (`CAP`) and close the connection; say why here
        if req.len() - 16 > BODY_CAP || count > SIGN_ITEMS_CAP {
            fatal(&format!(
                "SIGN of {count} queries ({} body bytes) is above the service's caps ({SIGN_ITEMS_CAP} items, \
                 {BODY_CAP} bytes): this trace cannot be signed",
                req.len() - 16
            ));
        }
        let mut conn = self.take();
        Self::send(&mut conn, OP_SIGN, count, req);
        conn
    }

    /// The answer to `sign_start`: the `count` answers (32 bytes each, in order) and the signature.
    pub fn sign_finish(&self, mut conn: UnixStream, count: usize, body_len: usize) -> (Vec<u8>, Sig) {
        let mut body = self.recv(&mut conn, OP_SIGN, count, body_len);
        self.put(conn);
        self.signs.fetch_add(1, Ordering::Relaxed);
        self.queries.fetch_add(count as u64, Ordering::Relaxed);
        self.query_bytes.fetch_add((body_len - 4 * count) as u64, Ordering::Relaxed);
        let m = count;
        if body.len() != 32 * m + 4772 {
            fatal(&format!("SIGN: response of {} bytes, expected {}", body.len(), 32 * m + 4772));
        }
        let s = &body[32 * m..];
        let idx = u32::from_le_bytes(s[..4].try_into().unwrap()) as u64;
        let d = |k: usize| -> Digest { s[4 + 32 * k..36 + 32 * k].try_into().unwrap() };
        let sig = Sig { idx, ots: (0..133).map(d).collect(), path: (133..149).map(d).collect() };
        body.truncate(32 * m);
        (body, sig)
    }

    /// The service's public key.
    pub fn vk(&self) -> Digest {
        let mut conn = self.take();
        let mut req = vec![0u8; 16];
        let body = self.call(&mut conn, OP_VK, 0, &mut req);
        self.put(conn);
        body.as_slice().try_into().unwrap_or_else(|_| fatal("VK: not 32 bytes"))
    }

    /// R9-PCS: run a call's `QUERY` batches over `conns`, at most one request in flight on each (the service reads a
    /// connection's next request only after answering the last, PROTOCOL.md §1): batch `k` goes out on connection
    /// `k mod m` once that connection's previous answer is read, and answers are read in batch order. With two
    /// connections the service computes the next batch while this thread reads one answer and sends the next request
    /// (one connection: the plain round trip). `send(conn)` writes the next batch and returns its `(first item, count,
    /// body bytes)`, or `None` when no item is left; `got(first, answers)` takes a batch's 32-byte answers.
    fn drive(
        &self,
        conns: &mut [UnixStream],
        mut send: impl FnMut(&mut UnixStream) -> Option<(usize, usize, usize)>,
        mut got: impl FnMut(usize, &[u8]),
    ) {
        let mut flight = std::collections::VecDeque::with_capacity(conns.len());
        for (c, conn) in conns.iter_mut().enumerate() {
            match send(conn) {
                Some(b) => flight.push_back((c, b)),
                None => break,
            }
        }
        while let Some((c, (first, count, body_len))) = flight.pop_front() {
            let body = self.recv(&mut conns[c], OP_QUERY, count, body_len);
            if body.len() != 32 * count {
                fatal(&format!("QUERY: {} answer bytes for {count} queries", body.len()));
            }
            got(first, &body);
            if let Some(b) = send(&mut conns[c]) {
                flight.push_back((c, b));
            }
        }
    }

    /// Items per batch for `n` items with at most `cap` a batch: the fewest batches, as even as can be, and at least
    /// `conns` batches when each still holds `SPLIT_MIN` items (so every connection has one).
    fn per_batch(n: usize, cap: usize, conns: usize) -> usize {
        let mut nb = n.div_ceil(cap.max(1)).max(1);
        if conns > 1 && n >= conns * SPLIT_MIN {
            nb = nb.max(conns);
        }
        n.div_ceil(nb).max(1)
    }

    /// `chunk[i] = H(q_{off+i})` on `conns`: `QUERY` batches of at most `BATCH_ITEMS` items and about
    /// `BATCH_BYTES` body bytes (`drive`).
    fn batches_on(&self, conns: &mut [UnixStream], off: usize, chunk: &mut [Digest], build: &Builder) {
        let bb = batch_bytes();
        let n = chunk.len();
        let per = Self::per_batch(n, BATCH_ITEMS, conns.len());
        let mut req: Vec<u8> = Vec::with_capacity(bb + (1 << 16));
        let mut i = 0;
        let send = |conn: &mut UnixStream| {
            if i >= n {
                return None;
            }
            req.clear();
            req.resize(16, 0);
            let start = i;
            let mut bytes = 0u64;
            while i < n && i - start < per && req.len() < bb {
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
            Self::send(conn, OP_QUERY, count, &mut req);
            self.queries.fetch_add(count as u64, Ordering::Relaxed);
            self.query_bytes.fetch_add(bytes, Ordering::Relaxed);
            Some((start, count, req.len() - 16))
        };
        let got = |first: usize, body: &[u8]| {
            for (o, a) in chunk[first..].iter_mut().zip(body.chunks_exact(32)) {
                *o = a.try_into().unwrap();
            }
        };
        self.drive(conns, send, got);
    }

    /// `batches_on` for the queries `0^pad ‖ row_i` (one length each), the body written by `writev` straight
    /// from `rows`: per item the shared `len ‖ 0^pad` prefix and the row. The same bytes on the socket as
    /// `batches_on` would write, in batches within the same size rule (at most `IOV_ITEMS` items).
    /// Items `0^pad ‖ rows[k·row_bytes + skip ..][.. row_bytes − skip]`: each row's tail behind `pad` zeros.
    #[allow(clippy::too_many_arguments)]
    fn row_batches_on(
        &self,
        conns: &mut [UnixStream],
        out: &mut [Digest],
        rows: &[u8],
        row_bytes: usize,
        pad: usize,
        skip: usize,
    ) {
        use std::io::IoSlice;
        /// 2 iovecs per item and the header stay within `IOV_MAX` = 1024.
        const IOV_ITEMS: usize = 511;
        let len = pad + row_bytes - skip;
        if len > QUERY_CAP {
            fatal(&format!("a query of {len} bytes is above the cap of {QUERY_CAP}"));
        }
        let mut prefix = vec![0u8; 4 + pad];
        prefix[..4].copy_from_slice(&(len as u32).to_le_bytes());
        // `batches_on` adds items while the request (16 + items) is below `batch_bytes()`
        let cap = ((batch_bytes().saturating_sub(17)) / (4 + len) + 1).min(BATCH_ITEMS).min(IOV_ITEMS);
        let n = out.len();
        let per = Self::per_batch(n, cap, conns.len());
        let mut i = 0;
        let send = |conn: &mut UnixStream| {
            if i >= n {
                return None;
            }
            let mut hdr = [0u8; 16];
            let count = per.min(n - i);
            let body_len = count * (4 + len);
            if body_len > BODY_CAP {
                fatal(&format!("a QUERY body of {body_len} bytes is above the cap of {BODY_CAP}"));
            }
            hdr[0] = OP_QUERY;
            hdr[4..8].copy_from_slice(&(count as u32).to_le_bytes());
            hdr[8..16].copy_from_slice(&(body_len as u64).to_le_bytes());
            let mut iov: Vec<IoSlice> = Vec::with_capacity(2 * count + 1);
            iov.push(IoSlice::new(&hdr));
            for k in i..i + count {
                iov.push(IoSlice::new(&prefix));
                iov.push(IoSlice::new(&rows[k * row_bytes + skip..][..row_bytes - skip]));
            }
            let mut bufs = &mut iov[..];
            while !bufs.is_empty() {
                match conn.write_vectored(bufs) {
                    Ok(0) => fatal(&format!("QUERY ({count} items, {body_len} bytes): write: zero bytes written")),
                    Ok(w) => IoSlice::advance_slices(&mut bufs, w),
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                    Err(e) => fatal(&format!("QUERY ({count} items, {body_len} bytes): write: {e}")),
                }
            }
            self.queries.fetch_add(count as u64, Ordering::Relaxed);
            self.query_bytes.fetch_add((count * len) as u64, Ordering::Relaxed);
            let first = i;
            i += count;
            Some((first, count, body_len))
        };
        let got = |first: usize, body: &[u8]| {
            for (o, a) in out[first..].iter_mut().zip(body.chunks_exact(32)) {
                *o = a.try_into().unwrap();
            }
        };
        self.drive(conns, send, got);
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
    /// One query (a Fiat–Shamir step, sequential): its own connection, kept non-blocking and
    /// polled, so the answer is taken as soon as it is written (the prover has nothing else to do
    /// meanwhile); the poll yields the CPU after a short spin.
    fn ask(&self, q: &[u8]) -> Digest {
        if q.len() > QUERY_CAP {
            fatal(&format!(
                "a Fiat–Shamir query of {} bytes is above queryCap = {QUERY_CAP} (the service refuses it)",
                q.len()
            ));
        }
        let mut req = Vec::with_capacity(20 + q.len());
        req.resize(16, 0);
        Self::push_item(&mut req, q);
        let mut g = self.fs.lock().unwrap();
        if g.is_none() {
            let c = open_stream(&self.path, &self.dir).unwrap_or_else(|e| fatal(&format!("connect {}: {e}", self.path)));
            c.set_nonblocking(true).unwrap_or_else(|e| fatal(&format!("socket: {e}")));
            *g = Some(c);
        }
        let conn = g.as_mut().unwrap();
        let len = req.len();
        req[4..8].copy_from_slice(&1u32.to_le_bytes());
        req[8..16].copy_from_slice(&((len - 16) as u64).to_le_bytes());
        req[0] = OP_QUERY;
        let mut sent = 0;
        let mut spins = 0u32;
        while sent < len {
            match conn.write(&req[sent..]) {
                Ok(k) => sent += k,
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => std::thread::yield_now(),
                Err(e) => fatal(&format!("QUERY ({len} bytes): write: {e}")),
            }
        }
        let mut buf = [0u8; 48];
        let mut got = 0;
        let mut want = 48;
        let mut msg = vec![];
        while got < want {
            match conn.read(&mut buf[got..want]) {
                Ok(0) => fatal("QUERY: the service closed the connection"),
                Ok(k) => {
                    got += k;
                    if got >= 16 && buf[0] != 0 {
                        // a refusal: its message is the body
                        let n = u64::from_le_bytes(buf[8..16].try_into().unwrap()) as usize;
                        msg.extend_from_slice(&buf[16..got]);
                        conn.set_nonblocking(false).ok();
                        let mut rest = vec![0u8; n.saturating_sub(msg.len())];
                        conn.read_exact(&mut rest).ok();
                        msg.extend_from_slice(&rest);
                        fatal(&format!(
                            "QUERY ({len} bytes) refused with status {} {}: {}",
                            buf[0],
                            status_name(buf[0]),
                            String::from_utf8_lossy(&msg)
                        ));
                    }
                    want = 48;
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    spins += 1;
                    if spins < 2000 {
                        std::hint::spin_loop();
                    } else {
                        std::thread::yield_now();
                    }
                }
                Err(e) => fatal(&format!("QUERY ({len} bytes): read: {e}")),
            }
        }
        drop(g);
        self.requests.fetch_add(1, Ordering::Relaxed);
        self.queries.fetch_add(1, Ordering::Relaxed);
        self.query_bytes.fetch_add(q.len() as u64, Ordering::Relaxed);
        if u64::from_le_bytes(buf[8..16].try_into().unwrap()) != 32 {
            fatal("QUERY: short answer");
        }
        buf[16..48].try_into().unwrap()
    }

    /// `out[i] = H(q_i)` on one pool connection, from the calling thread (each prover thread has its own).
    fn ask_many_here(&self, out: &mut [Digest], build: &Builder) {
        let mut conns = self.take_for(out.len());
        self.batches_on(&mut conns, 0, out, build);
        self.put_all(conns);
    }

    fn ask_rows_here(&self, out: &mut [Digest], rows: &[u8], row_bytes: usize, pad: usize) {
        let mut conns = self.take_for(out.len());
        self.row_batches_on(&mut conns, out, rows, row_bytes, pad, 0);
        self.put_all(conns);
    }

    fn ask_tails_here(&self, out: &mut [Digest], rows: &[u8], row_bytes: usize, skip: usize) {
        let mut conns = self.take_for(out.len());
        self.row_batches_on(&mut conns, out, rows, row_bytes, 0, skip);
        self.put_all(conns);
    }
}
