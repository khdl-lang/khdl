#[cfg(not(debug_assertions))]
use std::marker::PhantomData;

/// Wrapper around a type `T` that behaves as `T` when debug assertions are enabled,
/// and as `PhantomData<T>` when they're not.
///
/// This is useful to store debug-only check data, without any overhead when assertions are disabled.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct DebugOnly<T> {
    #[cfg(debug_assertions)]
    inner: T,
    #[cfg(not(debug_assertions))]
    inner: PhantomData<T>,
}

impl<T> DebugOnly<T> {
    pub fn new(f: impl FnOnce() -> T) -> Self {
        #[cfg(debug_assertions)]
        {
            DebugOnly { inner: f() }
        }

        #[cfg(not(debug_assertions))]
        {
            let _ = f;
            DebugOnly { inner: PhantomData }
        }
    }
}
