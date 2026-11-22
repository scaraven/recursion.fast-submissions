//! A stand-in for the `tracing` crate's `info_span!`, the only part leanVM's prover crates use.
//! A span is a named timer: with `LVM_PROF=1` every closed span adds its wall time to a table
//! that `report` prints (top-level spans of the same name are summed); otherwise it is free.

use std::sync::Mutex;
use std::sync::atomic::{AtomicU8, Ordering};
use std::time::Instant;

static ON: AtomicU8 = AtomicU8::new(2);
static MARKS: AtomicU8 = AtomicU8::new(2);
static TABLE: Mutex<Vec<(&'static str, f64, u64)>> = Mutex::new(Vec::new());

pub fn enabled() -> bool {
    match ON.load(Ordering::Relaxed) {
        2 => {
            let on = std::env::var("LVM_PROF").is_ok_and(|v| v == "1");
            ON.store(on as u8, Ordering::Relaxed);
            on
        }
        v => v == 1,
    }
}

/// lvm2 E2-K (ARCH-7 §2.5 item 3): with `LVM_SDE_MARKS=1`, the Keccak GKR's pass spans also execute Intel SDE
/// "SSC" markers (`mov ebx, mark; fs addr32 nop`, a no-op natively), so that `sde -control start:ssc:..` counts
/// one pass at a time. Mark `0x4c56_PP_0S`: `PP` the pass (1 Product, 2 Skip, 3 Groups, 4 Tables, 5 Tail, 6 the
/// whole layer of the tape; +16 for the E2 spans), `S` 1 at the start, 2 at the end. Off (one relaxed load) otherwise.
fn sde_pass(name: &str) -> u32 {
    let (base, e2) = match name.split_once('/') {
        Some((b, "E2")) => (b, 16),
        _ => (name, 0),
    };
    let p = match base {
        "Product" => 1,
        "Skip" => 2,
        "Groups" => 3,
        "Tables" => 4,
        "Tail" => 5,
        "Layer" => 6,
        _ => return 0,
    };
    0x4c56_0000 | (p + e2) << 8
}

/// One SSC marker; SDE reads the mark off the `mov ebx, imm32` before the `fs addr32 nop`, so each is a constant.
#[cfg(target_arch = "x86_64")]
macro_rules! ssc {
    ($m:expr) => {
        // SAFETY: rbx is saved and restored around the marker; the marker is a no-op outside SDE.
        unsafe {
            core::arch::asm!(
                "xchg {t}, rbx",
                "mov ebx, {m}",
                ".byte 0x64, 0x67, 0x90",
                "xchg {t}, rbx",
                m = const $m,
                t = inout(reg) 0u64 => _,
            )
        }
    };
}

#[inline(never)]
fn sde_mark(mark: u32) {
    #[cfg(target_arch = "x86_64")]
    match mark {
        0x4c560101 => ssc!(0x4c560101),
        0x4c560102 => ssc!(0x4c560102),
        0x4c561101 => ssc!(0x4c561101),
        0x4c561102 => ssc!(0x4c561102),
        0x4c560201 => ssc!(0x4c560201),
        0x4c560202 => ssc!(0x4c560202),
        0x4c561201 => ssc!(0x4c561201),
        0x4c561202 => ssc!(0x4c561202),
        0x4c560301 => ssc!(0x4c560301),
        0x4c560302 => ssc!(0x4c560302),
        0x4c561301 => ssc!(0x4c561301),
        0x4c561302 => ssc!(0x4c561302),
        0x4c560401 => ssc!(0x4c560401),
        0x4c560402 => ssc!(0x4c560402),
        0x4c561401 => ssc!(0x4c561401),
        0x4c561402 => ssc!(0x4c561402),
        0x4c560501 => ssc!(0x4c560501),
        0x4c560502 => ssc!(0x4c560502),
        0x4c561501 => ssc!(0x4c561501),
        0x4c561502 => ssc!(0x4c561502),
        0x4c560601 => ssc!(0x4c560601),
        0x4c560602 => ssc!(0x4c560602),
        0x4c561601 => ssc!(0x4c561601),
        0x4c561602 => ssc!(0x4c561602),
        _ => {}
    }
    #[cfg(not(target_arch = "x86_64"))]
    let _ = mark;
}

fn marks() -> bool {
    match MARKS.load(Ordering::Relaxed) {
        2 => {
            let on = std::env::var("LVM_SDE_MARKS").is_ok_and(|v| v == "1");
            MARKS.store(on as u8, Ordering::Relaxed);
            on
        }
        v => v == 1,
    }
}

fn mark(name: &str, end: bool) {
    if marks() {
        let m = sde_pass(name);
        if m != 0 {
            sde_mark(m | if end { 2 } else { 1 });
        }
    }
}

pub struct Span {
    name: &'static str,
    start: Option<Instant>,
    entered: bool,
}

impl Span {
    pub fn new(name: &'static str) -> Self {
        Self { name, start: None, entered: false }
    }
    pub fn in_scope<R>(&self, f: impl FnOnce() -> R) -> R {
        let t = enabled().then(Instant::now);
        mark(self.name, false);
        let r = f();
        mark(self.name, true);
        if let Some(t) = t {
            add(self.name, t.elapsed().as_secs_f64());
        }
        r
    }
    /// Timed from here to the drop.
    pub fn entered(mut self) -> Self {
        self.start = enabled().then(Instant::now);
        self.entered = true;
        mark(self.name, false);
        self
    }
}

impl Drop for Span {
    fn drop(&mut self) {
        // Only an entered span marks its end here (`in_scope` marks its own).
        if self.entered {
            mark(self.name, true);
        }
        if let Some(t) = self.start.take() {
            add(self.name, t.elapsed().as_secs_f64());
        }
    }
}

fn add(name: &'static str, s: f64) {
    let mut t = TABLE.lock().unwrap();
    match t.iter_mut().find(|e| e.0 == name) {
        Some(e) => {
            e.1 += s;
            e.2 += 1;
        }
        None => t.push((name, s, 1)),
    }
}

/// Process CPU seconds (all threads) and the oracle service's CPU seconds (`LVM_SVC_PID`, from
/// `/proc/<pid>/stat`, 10 ms ticks), for the per-stage `PCPU` lines of `LVM_PROF=1`.
pub fn cpu_now() -> (f64, f64) {
    #[repr(C)]
    struct Ts {
        s: i64,
        ns: i64,
    }
    unsafe extern "C" {
        fn clock_gettime(clk: i32, ts: *mut Ts) -> i32;
    }
    let mut t = Ts { s: 0, ns: 0 };
    unsafe { clock_gettime(2, &mut t) };
    let svc = std::env::var("LVM_SVC_PID").ok().and_then(|p| std::fs::read_to_string(format!("/proc/{p}/stat")).ok()).map_or(0.0, |st| {
        let f: Vec<&str> = st.rsplit(')').next().unwrap_or("").split_whitespace().collect();
        let tk = |i: usize| f.get(i).and_then(|x| x.parse::<f64>().ok()).unwrap_or(0.0);
        (tk(11) + tk(12)) / 100.0
    });
    (t.s as f64 + t.ns as f64 * 1e-9, svc)
}

/// Record a named interval measured elsewhere (the drivers' own stages).
pub fn record(name: &'static str, s: f64) {
    if enabled() {
        add(name, s);
    }
}

/// lvm2 E2-K: the span table as it stands (name, seconds, count), for per-run deltas.
pub fn snapshot() -> Vec<(&'static str, f64, u64)> {
    TABLE.lock().unwrap().clone()
}

pub fn report() -> String {
    let t = TABLE.lock().unwrap();
    t.iter().map(|(n, s, c)| format!("  span {n:<24} {:>9.3} s  ×{c}\n", s)).collect()
}

macro_rules! info_span {
    ($name:expr $(, $($rest:tt)*)?) => {
        $crate::lv::tracing::Span::new($name)
    };
}
pub(crate) use info_span;
