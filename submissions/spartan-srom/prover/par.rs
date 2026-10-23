//! Minimal data parallelism (no dependencies, so the build is offline): one persistent pool of
//! `threads() − 1` workers, started on first use and shared by every caller. A parallel call posts a
//! job of `n` chunks; the calling thread works on its own job too, idle workers take chunks of any
//! posted job, and the call returns when every chunk is done. Concurrent callers (the leaves of a
//! tree proved at once, `main.rs`) share the workers, and a chunk may itself make a parallel call.
//! Field sums are exact (XOR), so the split never changes a result.

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};

static THREADS: OnceLock<usize> = OnceLock::new();

pub fn threads() -> usize {
    *THREADS.get_or_init(|| {
        std::env::var("SPARTAN_THREADS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1))
            .max(1)
    })
}

/// A posted call: chunk `c < n` runs `f(c)`. `f` borrows the caller's stack; the caller does not
/// return before `done = n`, and a chunk is claimed (`next`) before `f` is read, so no worker reads
/// `f` after the call returned.
struct Job {
    f: *const (dyn Fn(usize) + Sync + 'static),
    n: usize,
    next: AtomicUsize,
    done: AtomicUsize,
    panicked: AtomicBool,
}

// SAFETY: `f` is `Sync` and only dereferenced while its caller waits (see `Job`).
unsafe impl Send for Job {}
unsafe impl Sync for Job {}

impl Job {
    /// Run chunks until none is left.
    fn work(&self) {
        loop {
            let c = self.next.fetch_add(1, Ordering::AcqRel);
            if c >= self.n {
                return;
            }
            // SAFETY: chunk `c` is claimed, so the caller is still waiting (see `Job`).
            let f = unsafe { &*self.f };
            if catch_unwind(AssertUnwindSafe(|| f(c))).is_err() {
                self.panicked.store(true, Ordering::Release);
            }
            self.done.fetch_add(1, Ordering::AcqRel);
        }
    }
}

struct Pool {
    jobs: Mutex<Vec<Arc<Job>>>,
    cv: Condvar,
    workers: usize,
}

fn pool() -> &'static Pool {
    static POOL: OnceLock<&'static Pool> = OnceLock::new();
    POOL.get_or_init(|| {
        let p: &'static Pool =
            Box::leak(Box::new(Pool { jobs: Mutex::new(Vec::new()), cv: Condvar::new(), workers: threads() - 1 }));
        for _ in 0..p.workers {
            std::thread::spawn(move || worker(p));
        }
        p
    })
}

fn worker(p: &'static Pool) {
    loop {
        let job = {
            let mut q = p.jobs.lock().unwrap();
            loop {
                q.retain(|j| j.next.load(Ordering::Acquire) < j.n);
                if let Some(j) = q.first() {
                    break j.clone();
                }
                q = p.cv.wait(q).unwrap();
            }
        };
        job.work();
    }
}

/// Start the pool's workers now (before a timed request).
pub fn warm() {
    if threads() > 1 {
        pool();
    }
}

/// Run `f(c)` for every `c < n`, in parallel on the pool and the calling thread.
pub fn run(n: usize, f: &(dyn Fn(usize) + Sync)) {
    if n <= 1 || threads() == 1 {
        (0..n).for_each(f);
        return;
    }
    let p = pool();
    // SAFETY: only the lifetime is erased; `run` returns after every use of `f` (see `Job`).
    let f: *const (dyn Fn(usize) + Sync + 'static) = unsafe { std::mem::transmute(f) };
    let job = Arc::new(Job { f, n, next: AtomicUsize::new(0), done: AtomicUsize::new(0), panicked: AtomicBool::new(false) });
    p.jobs.lock().unwrap().push(job.clone());
    for _ in 0..(n - 1).min(p.workers) {
        p.cv.notify_one();
    }
    job.work();
    let mut spins = 0u32;
    while job.done.load(Ordering::Acquire) < n {
        if spins < 64 {
            std::hint::spin_loop();
            spins += 1;
        } else {
            std::thread::yield_now();
        }
    }
    if job.panicked.load(Ordering::Acquire) {
        panic!("a parallel chunk panicked");
    }
}

fn nchunks(n: usize, min_chunk: usize) -> usize {
    match (n, threads()) {
        (0, _) => 0,
        (_, 1) => 1,
        (_, t) => (n / min_chunk.max(1)).clamp(1, 4 * t),
    }
}

/// Run `f(lo, hi)` over `[0, n)` split into chunks of at least `min_chunk`, in parallel, and
/// return the per-chunk results in order.
pub fn map_chunks<R: Send, F: Fn(usize, usize) -> R + Sync>(n: usize, min_chunk: usize, f: F) -> Vec<R> {
    let k = nchunks(n, min_chunk);
    let out: Vec<Mutex<Option<R>>> = (0..k).map(|_| Mutex::new(None)).collect();
    run(k, &|c| {
        let r = f(c * n / k, (c + 1) * n / k);
        *out[c].lock().unwrap() = Some(r);
    });
    out.into_iter().map(|r| r.into_inner().unwrap().unwrap()).collect()
}

/// Fill `out[i] = f(i)` in parallel.
pub fn fill<T: Send, F: Fn(usize) -> T + Sync>(out: &mut [T], min_chunk: usize, f: F) {
    for_each_chunk_mut(out, min_chunk, |base, chunk| {
        for (i, o) in chunk.iter_mut().enumerate() {
            *o = f(base + i);
        }
    });
}

/// A slice's base pointer, shared by the chunks that each take a disjoint part of it.
struct Base<T>(*mut T);
unsafe impl<T: Send> Sync for Base<T> {}

impl<T> Base<T> {
    fn at(&self, i: usize) -> *mut T {
        self.0.wrapping_add(i)
    }
}

/// Call `f(offset, chunk)` on disjoint mutable chunks of `out`, in parallel.
pub fn for_each_chunk_mut<T: Send, F: Fn(usize, &mut [T]) + Sync>(out: &mut [T], min_chunk: usize, f: F) {
    let n = out.len();
    let k = nchunks(n, min_chunk);
    if k <= 1 || threads() == 1 {
        f(0, out);
        return;
    }
    let size = n.div_ceil(k);
    let k = n.div_ceil(size);
    let base = Base(out.as_mut_ptr());
    run(k, &|c| {
        let lo = c * size;
        let len = size.min(n - lo);
        // SAFETY: the chunks `[c·size, c·size + len)` are disjoint and inside `out`, which is
        // borrowed mutably for the whole call.
        let chunk = unsafe { std::slice::from_raw_parts_mut(base.at(lo), len) };
        f(lo, chunk);
    });
}

/// Call `f(offset, chunk)` on disjoint mutable chunks of `out` whose offsets and lengths are
/// multiples of `align` (but the last length), in parallel, and return the results in order.
pub fn map_chunks_mut<T: Send, R: Send, F: Fn(usize, &mut [T]) -> R + Sync>(out: &mut [T], align: usize, min_chunk: usize, f: F) -> Vec<R> {
    let n = out.len();
    let k = nchunks(n, min_chunk.max(align));
    if k <= 1 {
        return vec![f(0, out)];
    }
    let size = n.div_ceil(k).div_ceil(align) * align;
    let k = n.div_ceil(size);
    let base = Base(out.as_mut_ptr());
    let res: Vec<Mutex<Option<R>>> = (0..k).map(|_| Mutex::new(None)).collect();
    run(k, &|c| {
        let lo = c * size;
        let len = size.min(n - lo);
        // SAFETY: as in `for_each_chunk_mut`.
        let chunk = unsafe { std::slice::from_raw_parts_mut(base.at(lo), len) };
        *res[c].lock().unwrap() = Some(f(lo, chunk));
    });
    res.into_iter().map(|r| r.into_inner().unwrap().unwrap()).collect()
}

/// `(0..n).map(f).collect()` in parallel, without a serial initialisation pass.
pub fn collect_vec<T: Send, F: Fn(usize) -> T + Sync>(n: usize, min_chunk: usize, f: F) -> Vec<T> {
    let mut v: Vec<T> = Vec::with_capacity(n);
    for_each_chunk_mut(&mut v.spare_capacity_mut()[..n], min_chunk, |off, chunk| {
        for (i, slot) in chunk.iter_mut().enumerate() {
            slot.write(f(off + i));
        }
    });
    // SAFETY: every slot in `[0, n)` was written exactly once above.
    unsafe { v.set_len(n) };
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_and_concurrent_calls() {
        let total = AtomicUsize::new(0);
        std::thread::scope(|s| {
            for _ in 0..3 {
                s.spawn(|| {
                    let v = map_chunks(1000, 1, |a, b| {
                        let inner: usize = map_chunks(b - a, 1, |x, y| y - x).into_iter().sum();
                        assert_eq!(inner, b - a);
                        (a..b).sum::<usize>()
                    });
                    total.fetch_add(v.into_iter().sum::<usize>(), Ordering::Relaxed);
                });
            }
        });
        assert_eq!(total.into_inner(), 3 * (999 * 1000 / 2));
        let v = collect_vec(10_000, 7, |i| i * i);
        assert!(v.iter().enumerate().all(|(i, &x)| x == i * i));
    }
}
