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
use crate::oracle::{Builder, Builder2, GrindJob, GrindWin, Oracle};
use crate::par;

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
pub const BATCH_BYTES: usize = 4 << 20;

/// Print the error and exit with status 3.
pub fn fatal(msg: &str) -> ! {
    eprintln!("flock-prover: oracle service: {msg}");
    std::process::exit(3)
}

struct Pool {
    idle: Vec<UnixStream>,
    open: usize,
}

/// A connection of the pipelined grinder (`Oracle::grind`), non-blocking for good, with the
/// response the last search no longer needed (its buffer and the bytes read so far): read to its
/// end, its status checked, and dropped before the connection's next request.
struct GConn {
    s: UnixStream,
    left: Option<(Vec<u8>, usize)>,
}

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}
const POLLIN: i16 = 1;

extern "C" {
    /// glibc's `poll(2)`.
    fn poll(fds: *mut PollFd, nfds: u64, timeout: i32) -> i32;
}

/// Wait until one of `fds` is readable: a short spin of non-blocking polls (the answer of a small
/// request comes back in tens of microseconds), then blocking polls of 1 ms, which leave the CPU
/// to the service.
fn wait_readable(fds: &mut [PollFd]) {
    static SPIN: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    let spin = *SPIN.get_or_init(|| std::env::var("FLOCK_GRIND_SPIN").ok().and_then(|v| v.parse().ok()).unwrap_or(64));
    let mut spins = 0u32;
    loop {
        for f in fds.iter_mut() {
            f.revents = 0;
        }
        // SAFETY: `fds` is a valid array of `pollfd` (`PollFd` has its C layout) of this length.
        let r = unsafe { poll(fds.as_mut_ptr(), fds.len() as u64, if spins < spin { 0 } else { 1 }) };
        if r > 0 {
            return;
        }
        if r < 0 {
            let e = std::io::Error::last_os_error();
            if e.kind() != std::io::ErrorKind::Interrupted {
                fatal(&format!("poll: {e}"));
            }
        }
        spins += 1;
    }
}

/// Write all of `req` to a non-blocking connection (the service reads a request whole before it
/// answers, and the connection has no response pending, so this cannot block both sides).
fn write_nb(c: &mut UnixStream, req: &[u8]) {
    let mut sent = 0;
    while sent < req.len() {
        match c.write(&req[sent..]) {
            Ok(k) => sent += k,
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => std::hint::spin_loop(),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => fatal(&format!("QUERY (grinding, {} bytes): write: {e}", req.len())),
        }
    }
}

/// Finish reading a response a search left in flight (`resp`, `got` bytes of it read) and drop it.
/// A refusal (its header says so, with a body shorter than the answers) is fatal with its message.
fn drain_nb(c: &mut UnixStream, mut resp: Vec<u8>, mut got: usize) {
    let fd = c.as_raw_fd();
    while got < resp.len() {
        if got >= 16 && resp[0] != 0 {
            let n = u64::from_le_bytes(resp[8..16].try_into().unwrap()) as usize;
            let mut msg = resp[16..got].to_vec();
            c.set_nonblocking(false).ok();
            let mut rest = vec![0u8; n.saturating_sub(msg.len())];
            c.read_exact(&mut rest).ok();
            msg.extend_from_slice(&rest);
            fatal(&format!("QUERY (grinding) refused with status {} {}: {}", resp[0], status_name(resp[0]), String::from_utf8_lossy(&msg)));
        }
        match c.read(&mut resp[got..]) {
            Ok(0) => fatal("QUERY (grinding): the service closed the connection"),
            Ok(k) => got += k,
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => wait_readable(&mut [PollFd { fd, events: POLLIN, revents: 0 }]),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => fatal(&format!("QUERY (grinding): read: {e}")),
        }
    }
    if u64::from_le_bytes(resp[8..16].try_into().unwrap()) as usize != resp.len() - 16 {
        fatal("QUERY (grinding): short answer");
    }
}

/// One request of the pipelined search in flight: batch `batch` (nonces `batch·B …`), at step
/// `step` (0 the absorbs, `s` the `s`-th squeezes), with every step's answers so far.
struct Flight {
    batch: u64,
    step: usize,
    steps: Vec<Vec<Digest>>,
    resp: Vec<u8>,
    got: usize,
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
    /// the pipelined grinder's connections (`Oracle::grind`)
    gconns: Mutex<Vec<GConn>>,
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
            gconns: Mutex::new(Vec::new()),
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
        let mut req = vec![0u8; 16];
        for q in qs {
            Self::push_item(&mut req, q);
        }
        let conn = self.sign_start(&mut req, qs.len());
        let (body, sig) = self.sign_finish(conn, qs.len(), req.len() - 16);
        (body.chunks_exact(32).map(|a| a.try_into().unwrap()).collect(), sig)
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

    /// The grinder's sub-batches (`Fs::grind`): one `QUERY` per batch, each on its own pool connection,
    /// all written from this thread and then read by polling the connections without blocking (as
    /// `ask` does), so a step costs one round trip and no thread wake-up. A batch must fit one request
    /// (`BATCH_ITEMS`, `BODY_CAP`).
    fn ask_batches(&self, outs: &mut [Vec<Digest>], build: &Builder2) {
        let nb = outs.len();
        let mut conns: Vec<UnixStream> = (0..nb).map(|_| self.take()).collect();
        let mut nbytes = 0u64;
        let mut req: Vec<u8> = Vec::new();
        for (b, conn) in conns.iter_mut().enumerate() {
            let count = outs[b].len();
            if count > BATCH_ITEMS {
                fatal(&format!("a grinding batch of {count} queries is above {BATCH_ITEMS}"));
            }
            req.clear();
            req.resize(16, 0);
            for i in 0..count {
                let lp = req.len();
                req.extend_from_slice(&[0u8; 4]);
                build(b, i, &mut req);
                let len = req.len() - lp - 4;
                if len > QUERY_CAP {
                    fatal(&format!("a query of {len} bytes is above the cap of {QUERY_CAP}"));
                }
                req[lp..lp + 4].copy_from_slice(&(len as u32).to_le_bytes());
                nbytes += len as u64;
            }
            if req.len() - 16 > BODY_CAP {
                fatal(&format!("a QUERY body of {} bytes is above the cap of {BODY_CAP}", req.len() - 16));
            }
            Self::send(conn, OP_QUERY, count, &mut req);
            conn.set_nonblocking(true).unwrap_or_else(|e| fatal(&format!("socket: {e}")));
        }
        // poll every connection until each holds its whole response (header, then 32 B an answer)
        let mut bufs: Vec<Vec<u8>> = outs.iter().map(|o| vec![0u8; 16 + 32 * o.len()]).collect();
        let mut got = vec![0usize; nb];
        let mut left = nb;
        let mut spins = 0u32;
        while left > 0 {
            let mut progress = false;
            for b in 0..nb {
                let want = bufs[b].len();
                if got[b] == want {
                    continue;
                }
                match conns[b].read(&mut bufs[b][got[b]..]) {
                    Ok(0) => fatal("QUERY (grinding): the service closed the connection"),
                    Ok(k) => {
                        got[b] += k;
                        progress = true;
                        if got[b] >= 16 && bufs[b][0] != 0 {
                            let n = u64::from_le_bytes(bufs[b][8..16].try_into().unwrap()) as usize;
                            let mut msg = bufs[b][16..got[b]].to_vec();
                            conns[b].set_nonblocking(false).ok();
                            let mut rest = vec![0u8; n.saturating_sub(msg.len())];
                            conns[b].read_exact(&mut rest).ok();
                            msg.extend_from_slice(&rest);
                            fatal(&format!("QUERY (grinding) refused with status {} {}: {}", bufs[b][0], status_name(bufs[b][0]), String::from_utf8_lossy(&msg)));
                        }
                        if got[b] == want {
                            left -= 1;
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
                    Err(e) => fatal(&format!("QUERY (grinding): read: {e}")),
                }
            }
            if !progress {
                spins += 1;
                if spins < 2000 {
                    std::hint::spin_loop();
                } else {
                    std::thread::yield_now();
                }
            }
        }
        for (b, conn) in conns.into_iter().enumerate() {
            conn.set_nonblocking(false).unwrap_or_else(|e| fatal(&format!("socket: {e}")));
            if u64::from_le_bytes(bufs[b][8..16].try_into().unwrap()) as usize != 32 * outs[b].len() {
                fatal("QUERY (grinding): short answer");
            }
            for (i, o) in outs[b].iter_mut().enumerate() {
                *o = bufs[b][16 + 32 * i..48 + 32 * i].try_into().unwrap();
            }
            self.put(conn);
        }
        let n: usize = outs.iter().map(|o| o.len()).sum();
        self.requests.fetch_add(nb as u64, Ordering::Relaxed);
        self.queries.fetch_add(n as u64, Ordering::Relaxed);
        self.query_bytes.fetch_add(nbytes, Ordering::Relaxed);
    }

    /// **The pipelined search** (PD). Batches of `B` consecutive nonces, `depth` of them in flight,
    /// each on its own grinder connection: a batch's next step (its squeezes) is sent as soon as its
    /// previous answers arrive, and a connection whose batch is done starts the next batch at once.
    /// Batch `j` is decided when it and every batch below it have finished; the first batch with a
    /// winner gives its smallest winning nonce, which is then the smallest winning nonce overall,
    /// whatever the order the answers came in. No batch above a known winner is started; requests
    /// still in flight at the end are left to finish and their answers dropped before the
    /// connection's next use.
    fn grind(&self, job: &GrindJob) -> Option<GrindWin> {
        let (b, d, nsq) = (job.batch, job.depth.min(16), job.nsq);
        let alen = job.pre.len() + crate::params::NONCE_LEN;
        if b > BATCH_ITEMS || b * (4 + alen) > BODY_CAP || alen > QUERY_CAP {
            return None;
        }
        let mut g = self.gconns.lock().unwrap();
        while g.len() < d {
            let c = self.take();
            c.set_nonblocking(true).unwrap_or_else(|e| fatal(&format!("socket: {e}")));
            g.push(GConn { s: c, left: None });
        }
        for c in g.iter_mut() {
            if let Some((resp, got)) = c.left.take() {
                drain_nb(&mut c.s, resp, got);
            }
        }
        let comp = |n: usize| 1 + n.div_ceil(64) as u64;
        let (mut nreq, mut nq, mut nbytes, mut comps, mut launched) = (0u64, 0u64, 0u64, 0u64, 0u64);
        let mut req: Vec<u8> = Vec::with_capacity(16 + b * (4 + alen));
        let mut send = |c: &mut UnixStream, f: &Flight, req: &mut Vec<u8>| {
            req.clear();
            req.resize(16, 0);
            if f.step == 0 {
                for i in 0..b {
                    req.extend_from_slice(&(alen as u32).to_le_bytes());
                    req.extend_from_slice(job.pre);
                    req.extend_from_slice(&crate::transcript::nonce_bytes(f.batch * b as u64 + i as u64));
                }
                nbytes += (b * alen) as u64;
                comps += b as u64 * comp(alen);
            } else {
                for a in &f.steps[f.step - 1] {
                    req.extend_from_slice(&40u32.to_le_bytes());
                    req.extend_from_slice(crate::params::TAG_SQZ);
                    req.extend_from_slice(a);
                }
                nbytes += 40 * b as u64;
                comps += b as u64 * comp(40);
            }
            let body_len = req.len() - 16;
            req[0] = OP_QUERY;
            req[4..8].copy_from_slice(&(b as u32).to_le_bytes());
            req[8..16].copy_from_slice(&(body_len as u64).to_le_bytes());
            write_nb(c, req);
            nreq += 1;
            nq += b as u64;
        };
        // `fl[c]`: connection c's request in flight; `res[j]`: batch j's result once finished
        let mut fl: Vec<Option<Flight>> = (0..d).map(|_| None).collect();
        let mut res: Vec<Option<Option<(usize, Vec<Digest>)>>> = Vec::new();
        let (mut base, mut next, mut won_at) = (0u64, 0u64, u64::MAX);
        let win = 'search: loop {
            // start batches on idle connections, never above a known winner
            for c in 0..d {
                if fl[c].is_none() && next < won_at {
                    let f = Flight { batch: next, step: 0, steps: Vec::with_capacity(nsq + 1), resp: vec![0u8; 16 + 32 * b], got: 0 };
                    send(&mut g[c].s, &f, &mut req);
                    fl[c] = Some(f);
                    next += 1;
                    launched += 1;
                }
            }
            let live: Vec<usize> = (0..d).filter(|&c| fl[c].is_some()).collect();
            let mut fds: Vec<PollFd> = live.iter().map(|&c| PollFd { fd: g[c].s.as_raw_fd(), events: POLLIN, revents: 0 }).collect();
            wait_readable(&mut fds);
            for (k, &c) in live.iter().enumerate() {
                if fds[k].revents == 0 {
                    continue;
                }
                let f = fl[c].as_mut().unwrap();
                loop {
                    match g[c].s.read(&mut f.resp[f.got..]) {
                        Ok(0) => fatal("QUERY (grinding): the service closed the connection"),
                        Ok(n) => {
                            f.got += n;
                            if f.got >= 16 && f.resp[0] != 0 {
                                let n = u64::from_le_bytes(f.resp[8..16].try_into().unwrap()) as usize;
                                let mut msg = f.resp[16..f.got].to_vec();
                                g[c].s.set_nonblocking(false).ok();
                                let mut rest = vec![0u8; n.saturating_sub(msg.len())];
                                g[c].s.read_exact(&mut rest).ok();
                                msg.extend_from_slice(&rest);
                                fatal(&format!("QUERY (grinding) refused with status {} {}: {}", f.resp[0], status_name(f.resp[0]), String::from_utf8_lossy(&msg)));
                            }
                            if f.got == f.resp.len() {
                                break;
                            }
                        }
                        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
                        Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                        Err(e) => fatal(&format!("QUERY (grinding): read: {e}")),
                    }
                }
                if f.got < f.resp.len() {
                    continue;
                }
                if u64::from_le_bytes(f.resp[8..16].try_into().unwrap()) as usize != 32 * b {
                    fatal("QUERY (grinding): short answer");
                }
                f.steps.push(f.resp[16..].chunks_exact(32).map(|a| a.try_into().unwrap()).collect());
                f.got = 0;
                if f.step < nsq {
                    f.step += 1;
                    let f = fl[c].as_ref().unwrap();
                    send(&mut g[c].s, f, &mut req);
                    continue;
                }
                // batch finished: its smallest winner, if any
                let f = fl[c].take().unwrap();
                let j = f.batch as usize;
                if res.len() <= j {
                    res.resize(j + 1, None);
                }
                let w = f.steps[nsq].iter().position(|a| a[crate::params::POW_BYTE] == 0);
                if w.is_some() {
                    won_at = won_at.min(f.batch);
                }
                res[j] = Some(w.map(|i| (i, (0..=nsq).map(|s| f.steps[s][i]).collect())));
                while let Some(Some(r)) = res.get(base as usize) {
                    match r {
                        Some((i, ans)) => break 'search (base * b as u64 + *i as u64, ans.clone()),
                        None => base += 1,
                    }
                }
            }
        };
        // the requests still in flight: their answers are dropped before the next use
        for c in 0..d {
            if let Some(f) = fl[c].take() {
                g[c].left = Some((f.resp, f.got));
            }
        }
        drop(g);
        self.requests.fetch_add(nreq, Ordering::Relaxed);
        self.queries.fetch_add(nq, Ordering::Relaxed);
        self.query_bytes.fetch_add(nbytes, Ordering::Relaxed);
        let (nonce, ans) = win;
        Some(GrindWin { nonce, abs: ans[0], sq: ans[1..].to_vec(), attempts: launched * b as u64, queries: nq, compressions: comps, rounds: nreq })
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
