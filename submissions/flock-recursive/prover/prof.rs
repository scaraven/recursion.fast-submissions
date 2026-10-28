//! Sub-phase timers for measurements (`FLOCK_PROF=1`): `span("name")` adds the time until it is
//! dropped to `name`'s total; `report()` lists the totals in first-use order and clears them. Off by
//! default; never touches the proof.

use std::sync::{Mutex, OnceLock};
use std::time::Instant;

static LOG: Mutex<Vec<(&'static str, f64)>> = Mutex::new(Vec::new());

pub fn on() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("FLOCK_PROF").is_some())
}

pub struct Span(&'static str, Option<Instant>);

pub fn span(name: &'static str) -> Span {
    Span(name, if on() { Some(Instant::now()) } else { None })
}

impl Drop for Span {
    fn drop(&mut self) {
        if let Some(t) = self.1 {
            let s = t.elapsed().as_secs_f64();
            let mut l = LOG.lock().unwrap();
            match l.iter_mut().find(|x| x.0 == self.0) {
                Some(x) => x.1 += s,
                None => l.push((self.0, s)),
            }
        }
    }
}

pub fn report() -> String {
    let mut l = LOG.lock().unwrap();
    let s = l.iter().map(|(n, s)| format!("{n}={s:.3}")).collect::<Vec<_>>().join(" ");
    l.clear();
    s
}
