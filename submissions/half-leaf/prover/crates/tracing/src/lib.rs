//! No-op `info_span!` (the only `tracing` API leanVM's experimental prover crates use). The span's fields are
//! evaluated by reference only (so the variables they name count as used) and dropped; nothing is recorded.

/// A span that records nothing.
#[derive(Clone, Copy, Debug, Default)]
pub struct Span;

/// The guard of an entered [`Span`].
#[derive(Debug)]
pub struct Entered;

impl Span {
    #[inline(always)]
    pub fn in_scope<T>(&self, f: impl FnOnce() -> T) -> T {
        f()
    }

    #[inline(always)]
    #[must_use]
    pub fn entered(self) -> Entered {
        Entered
    }

    #[inline(always)]
    #[must_use]
    pub fn enter(&self) -> Entered {
        Entered
    }
}

/// `info_span!(name, field, key = value, ..)`.
#[macro_export]
macro_rules! info_span {
    ($name:expr $(,)?) => {{
        let _ = &$name;
        $crate::Span
    }};
    ($name:expr, $($fields:tt)+) => {{
        let _ = &$name;
        $crate::__span_fields!($($fields)+);
        $crate::Span
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __span_fields {
    () => {};
    ($k:ident = $v:expr $(, $($rest:tt)*)?) => {
        let _ = &$v;
        $($crate::__span_fields!($($rest)*);)?
    };
    ($k:ident $(, $($rest:tt)*)?) => {
        let _ = &$k;
        $($crate::__span_fields!($($rest)*);)?
    };
}
