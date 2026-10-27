//! The global allocator: small allocations go to glibc; allocations of at least 8 MiB come from a
//! cache of page-aligned blocks that are never returned to the kernel, so a request's large
//! buffers reuse pages that are already faulted in (K §3's pre-faulted arena, as an allocator).
//! `prefault(bytes)` maps and touches one block before the timed part of a request; later large
//! allocations are carved from it (best fit, split), and freed blocks go back to the cache.
//! No effect on any result.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::Mutex;

const BIG: usize = 8 << 20;
const PAGE: usize = 4096;

pub struct Cache;

struct State {
    /// free blocks `(address, bytes)`
    free: Vec<(usize, usize)>,
    /// live blocks handed out `(address, bytes)`
    live: Vec<(usize, usize)>,
    mapped: usize,
}

static STATE: Mutex<State> = Mutex::new(State { free: Vec::new(), live: Vec::new(), mapped: 0 });

fn round(n: usize) -> usize {
    n.div_ceil(PAGE) * PAGE
}

unsafe fn map(bytes: usize) -> *mut u8 {
    System.alloc(Layout::from_size_align_unchecked(bytes, PAGE))
}

unsafe impl GlobalAlloc for Cache {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if l.size() < BIG || l.align() > PAGE {
            return System.alloc(l);
        }
        let need = round(l.size());
        let mut st = STATE.lock().unwrap();
        // best fit
        let mut best: Option<usize> = None;
        for (i, &(_, sz)) in st.free.iter().enumerate() {
            if sz >= need && best.map_or(true, |b| sz < st.free[b].1) {
                best = Some(i);
            }
        }
        if let Some(i) = best {
            let (a, sz) = st.free.swap_remove(i);
            if sz - need >= BIG {
                st.free.push((a + need, sz - need));
                st.live.push((a, need));
            } else {
                st.live.push((a, sz));
            }
            return a as *mut u8;
        }
        drop(st);
        let p = map(need);
        if p.is_null() {
            return p;
        }
        let mut st = STATE.lock().unwrap();
        st.mapped += need;
        st.live.push((p as usize, need));
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        if l.size() < BIG || l.align() > PAGE {
            return System.dealloc(p, l);
        }
        let mut st = STATE.lock().unwrap();
        let a = p as usize;
        let i = st.live.iter().position(|e| e.0 == a).expect("unknown large block");
        let (_, sz) = st.live.swap_remove(i);
        // merge with a free neighbour that follows or precedes it
        let mut blk = (a, sz);
        loop {
            if let Some(j) = st.free.iter().position(|e| e.0 == blk.0 + blk.1) {
                let (_, s2) = st.free.swap_remove(j);
                blk.1 += s2;
            } else if let Some(j) = st.free.iter().position(|e| e.0 + e.1 == blk.0) {
                let (a2, s2) = st.free.swap_remove(j);
                blk = (a2, s2 + blk.1);
            } else {
                break;
            }
        }
        st.free.push(blk);
    }
}

/// Map and touch `bytes` now (before a request's clock), as one cached free block.
pub fn prefault(bytes: usize) {
    let need = round(bytes);
    unsafe {
        let p = map(need);
        if p.is_null() {
            return;
        }
        let ptr = crate::par::SyncPtr(p);
        let pages = need / PAGE;
        crate::par::run(64, &|c| {
            let ptr = ptr;
            for i in (c * pages / 64)..((c + 1) * pages / 64) {
                std::ptr::write_volatile(ptr.0.add(i * PAGE), 0);
            }
        });
        let mut st = STATE.lock().unwrap();
        st.mapped += need;
        st.free.push((p as usize, need));
    }
}

/// Bytes mapped by the cache.
pub fn mapped() -> usize {
    STATE.lock().unwrap().mapped
}
