//! Rye is a minimal, x86-64-only experiment into adding fibers to Rust.
//!
//! Rye exposes an API that allows spawning, scheduling, and deallocating fibers. This API, while
//! largely safe, rests on a lot of unsafe assumptions not necessarily guarenteed by the rust
//! compiler. This is just an experiment and you should not use it for anything critical.
//!
//! Rye has no central place where fibers are registered. Instead, when a fiber is yielded to it
//! receives a handle to the yielding fiber.
//!
//! # Example
//!
//! ```
//! use rye::{Fiber, AllocStack};
//!
//! // Create the fiber
//! let (stack, fiber) = Fiber::spawn(AllocStack::new(4096), |main| {
//!     println!("Hello from fiber!");
//!     main.yield_to();
//! });
//!
//! // Yield to the fiber and return. This prints:
//! //  Hello from main!
//! //  Hello from fiber!
//! //  Back to main!
//! println!("Hello from main!");
//! let fiber = fiber.yield_to();
//! println!("Back to main!");
//!
//! // Reclaim stack to deallocate fiber
//! stack.reclaim(fiber);
//! ```

use std::{
    alloc::{alloc, dealloc, Layout},
    ffi::c_void,
    mem::ManuallyDrop,
    panic::{catch_unwind, AssertUnwindSafe},
    process::abort,
    ptr,
};

extern "C" {
    fn enter_fiber(
        stack: *mut u8,
        func: extern "C" fn(prev: *mut FiberCont, data: *mut c_void),
        data: *mut c_void,
    ) -> *mut FiberCont;

    fn yield_fiber(fiber: *mut FiberCont) -> *mut FiberCont;
}

enum FiberCont {}

/// A lightweight thread for cooperative multitasking.
///
/// Unlike a thread, a fiber must be yielded to in order to run. Other threads will not be preempted
/// for this to run.
pub struct Fiber {
    fiber: *mut FiberCont,
}

impl Fiber {
    unsafe fn from_raw(fiber: *mut FiberCont) -> Self {
        Fiber { fiber }
    }

    /// Creates a new fiber that runs the given closure on the given stack.
    ///
    /// Control must never reach the end of the function and panics may not propagate unhandled to
    /// the top of the fiber. Should the function return or a unhandled panic propagate through, the
    /// program will abort.
    ///
    /// Instead, a fiber may halt by yielding to another fiber and letting that other fiber
    /// reclaiming the stack using the `FiberStack` returned when the fiber was spawned.
    pub fn spawn<S, F>(stack: S, f: F) -> (FiberStack<S>, Fiber)
    where
        S: StackBytes,
        F: FnOnce(Fiber) + 'static,
    {
        extern "C" fn exec<F>(prev: *mut FiberCont, f: *mut c_void)
        where
            F: FnOnce(Fiber) + 'static,
        {
            let (f, fiber) =
                unsafe { (ptr::read(f as *mut F), Fiber::from_raw(yield_fiber(prev))) };

            match catch_unwind(AssertUnwindSafe(|| (f)(fiber))) {
                Ok(()) => eprintln!("Aborting: Control reached end of fiber"),
                Err(err) => eprintln!("Aborting: Unhandled panic in fiber: {:?}", err),
            }

            abort()
        }

        unsafe {
            let (lo, hi) = stack.bytes();
            assert!(lo as usize % 16 == 0, "Stack must be aligned to 16 bytes");
            assert!(lo < hi, "Stack must be non-empty");

            let mut f = ManuallyDrop::new(f);
            let result = enter_fiber(hi, exec::<F>, &mut *f as *mut _ as *mut c_void);

            (
                FiberStack(ManuallyDrop::new(stack)),
                Fiber::from_raw(result),
            )
        }
    }

    /// Stops the execution of the calling fiber and switches control to the given fiber.
    ///
    /// This method returns once another fiber yields to the calling fiber. The return value is then
    /// the fiber that yielded to the calling fiber.
    pub fn yield_to(self) -> Fiber {
        unsafe { Fiber::from_raw(yield_fiber(self.fiber)) }
    }
}

/// A stack that is in use by a fiber. This can be used to reclaim the original original stack `S`
/// once the fiber executing on the stack has stopped.
pub struct FiberStack<S>(ManuallyDrop<S>);

impl<S: StackBytes> FiberStack<S> {
    /// Whether the given fiber is contained within this stack.
    pub fn contains(&self, fiber: &Fiber) -> bool {
        let fiber = fiber.fiber as *const _;
        let (lo, hi) = self.0.bytes();
        fiber >= lo && fiber < hi
    }

    /// Reclaims the underlying stack.
    ///
    /// Makes no checks to verify that the fiber on the stack has stopped.
    ///
    /// Prefer using `reclaim` or `reclaim_unsafe` if possible.
    ///
    /// # Safety
    ///
    /// You must ensure that no fiber is executing on the given stack. Failure to ensure this will
    /// result in undefined behavior.
    pub unsafe fn reclaim_unchecked(self) -> S {
        ManuallyDrop::into_inner(self.0)
    }

    /// Reclaims the stack the given fiber is executing on.
    ///
    /// # Panics
    ///
    /// Will panic if the given fiber is not executing on this stack.
    pub fn reclaim(self, fiber: Fiber) -> S {
        assert!(self.contains(&fiber), "Fiber must be within stack");
        unsafe { self.reclaim_unchecked() }
    }
}

/// A byte slice suitable for executing a fiber on.
pub unsafe trait StackBytes {
    /// Returns a range of bytes for executing a fiber on. The following conditions must be met for
    /// the returned tuple `(lo, hi)`:
    ///
    /// 1. The byte range [`lo`, `hi`[ must be readble and writable memory.
    /// 2. `lo` and `hi` must be aligned to 16 bytes.
    /// 3. `lo` must be greater than `hi`.
    /// 4. Every call to `bytes` for a given `StackBytes` instance must result in the same values
    ///    returned for `lo` and `hi`.
    /// 5. The instance must have unique ownership over the range of bytes in [`lo`, `hi`[.
    /// 6. The range must remain readable and writable if the `StackBytes` instance is moved.
    fn bytes(&self) -> (*mut u8, *mut u8);
}

/// A stack slice that is allocated on the heap.
pub struct AllocStack {
    ptr: *mut u8,
    layout: Layout,
}

impl AllocStack {
    /// Allocates a new `AllocStack` on the heap.
    ///
    /// # Panics
    ///
    /// Panics if `size` is 0 or `size` rounded up to nearest multiple of 16 overflows `usize`.
    pub fn new(size: usize) -> AllocStack {
        assert!(size > 0);
        let layout = Layout::from_size_align(size, 16).unwrap();
        unsafe {
            AllocStack {
                ptr: alloc(layout),
                layout,
            }
        }
    }
}

impl Drop for AllocStack {
    fn drop(&mut self) {
        unsafe { dealloc(self.ptr, self.layout) }
    }
}

unsafe impl StackBytes for AllocStack {
    fn bytes(&self) -> (*mut u8, *mut u8) {
        unsafe { (self.ptr, self.ptr.add(self.layout.size())) }
    }
}

unsafe impl Send for AllocStack {}

unsafe impl Sync for AllocStack {}

#[cfg(test)]
mod std_tests {
    use super::{AllocStack, Fiber, FiberStack};
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        cell::{Cell, RefCell},
        panic::{RefUnwindSafe, UnwindSafe},
        rc::Rc,
    };

    assert_not_impl_any!(Fiber: Send);
    assert_impl_all!(Fiber: Unpin, UnwindSafe, RefUnwindSafe);
    assert_impl_all!(AllocStack: Send, Sync, Unpin, UnwindSafe, RefUnwindSafe);

    fn stack() -> AllocStack {
        AllocStack::new(16384)
    }

    #[derive(Clone)]
    struct Tester(Rc<Cell<usize>>);

    impl Tester {
        fn new() -> Self {
            Tester(Rc::new(Cell::new(0)))
        }

        fn step(&self, expected: usize) {
            assert_eq!(self.0.get(), expected);
            self.0.set(self.0.get() + 1);
        }

        fn spawn<F>(&self, f: F) -> (FiberStack<AllocStack>, Fiber)
        where
            F: FnOnce(Tester, Fiber) + 'static,
        {
            let this = self.clone();
            Fiber::spawn(stack(), move |fib| f(this, fib))
        }
    }

    #[test]
    fn basic() {
        let tester = Tester::new();

        tester.step(0);

        let (stack, fiber) = tester.spawn(move |tester, prev| {
            tester.step(2);
            prev.yield_to();
        });

        tester.step(1);
        let fiber = fiber.yield_to();
        tester.step(3);
        stack.reclaim(fiber);
    }

    #[test]
    fn yield_in_fiber() {
        let tester = Tester::new();

        let (s1, f1) = tester.spawn(move |tester, prev| {
            tester.step(2);
            prev.yield_to();
        });

        let (s2, f2) = tester.spawn(move |tester, prev| {
            tester.step(1);
            let f1 = f1.yield_to();
            tester.step(3);
            s1.reclaim(f1);
            prev.yield_to();
        });

        tester.step(0);
        let f2 = f2.yield_to();
        tester.step(4);
        s2.reclaim(f2);
    }

    #[test]
    fn ping_pong() {
        let tester = Tester::new();

        let (s1, f1) = tester.spawn(move |tester, f2| {
            tester.step(2);
            let f2 = f2.yield_to();
            tester.step(4);
            let f2 = f2.yield_to();
            tester.step(6);
            f2.yield_to();
        });

        let (s2, f2) = tester.spawn(move |tester, main| {
            tester.step(1);
            let f1 = f1.yield_to();
            tester.step(3);
            let f1 = f1.yield_to();
            tester.step(5);
            let f1 = f1.yield_to();
            tester.step(7);
            s1.reclaim(f1);
            main.yield_to();
        });

        tester.step(0);
        let f2 = f2.yield_to();
        tester.step(8);
        s2.reclaim(f2);
    }

    #[test]
    fn spawn_in_fiber() {
        let tester = Tester::new();

        let (s1, f1) = tester.spawn(move |tester, main| {
            let (s2, f2) = tester.spawn(move |tester, f1| {
                tester.step(2);
                f1.yield_to();
            });

            tester.step(1);
            let f2 = f2.yield_to();
            tester.step(3);
            s2.reclaim(f2);
            main.yield_to();
        });

        tester.step(0);
        let f1 = f1.yield_to();
        tester.step(4);
        s1.reclaim(f1);
    }

    #[test]
    fn yield_from_inner_to_main() {
        let tester = Tester::new();
        let s1_send = Rc::new(RefCell::<Option<FiberStack<AllocStack>>>::new(None));
        let s2_send = Rc::new(RefCell::new(None));
        let s1_recv = s1_send.clone();
        let s2_recv = s2_send.clone();

        let (s1, f1) = tester.spawn(move |tester, main| {
            let (s2, f2) = tester.spawn(move |tester, f1| {
                tester.step(2);
                (*s1_recv).borrow_mut().take().unwrap().reclaim(f1);
                main.yield_to();
            });

            *s2_send.borrow_mut() = Some(s2);
            tester.step(1);
            f2.yield_to();
        });

        *s1_send.borrow_mut() = Some(s1);

        tester.step(0);
        let f2 = f1.yield_to();
        (*s2_recv).borrow_mut().take().unwrap().reclaim(f2);
        tester.step(3);
    }
}
