//! A `#[global_allocator]` that counts, per thread, what passed through it.
//!
//! Per thread rather than globally so that `cargo test`'s parallel harness
//! cannot make one test's allocations show up in another's measurement. The
//! counters live in a `const`-initialised `Cell` of a `Copy` struct: reading or
//! writing them allocates nothing and registers no TLS destructor, which is
//! what makes it safe to touch them from inside `alloc` itself.
//!
//! Sizes matter as much as counts here. A `Box<AList<T>>` allocation is exactly
//! `size_of::<AList<T>>()` bytes, while the slots `Vec` allocations are
//! `capacity * size_of::<AList<T>>()`, so counting allocations *of the node
//! size* separates "a bucket node was built" from "the table was allocated"
//! without needing access to the hashmap's private internals.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

/// How many distinct allocation sizes [`Counts`] remembers before it stops
/// recording new ones. Five is enough to hold a whole `Vec` doubling chain.
pub const SIZE_SLOTS: usize = 12;

#[derive(Clone, Copy)]
pub struct Counts {
    /// Every call that handed back fresh memory (`alloc`, `alloc_zeroed`, and
    /// the new half of a `realloc`).
    pub allocs: usize,
    /// Every call that gave memory back (`dealloc`, and the old half of a
    /// `realloc`).
    pub deallocs: usize,
    /// Bytes requested by the calls counted in `allocs`.
    pub bytes: usize,
    /// Allocations whose requested size was exactly `watch_size`.
    pub watch_hits: usize,
    /// The size singled out by `watch_hits`; `usize::MAX` matches nothing.
    pub watch_size: usize,
    /// The distinct sizes seen, in first-seen order, and how many of each.
    pub sizes: [usize; SIZE_SLOTS],
    pub size_counts: [usize; SIZE_SLOTS],
    pub sizes_len: usize,
    /// Set when a size was seen that no longer fit in `sizes`.
    pub sizes_overflowed: bool,
    /// Off until [`measure`] arms it, so that allocations made outside a
    /// measured region are ignored entirely.
    pub armed: bool,
}

impl Counts {
    pub const ZERO: Counts = Counts {
        allocs: 0,
        deallocs: 0,
        bytes: 0,
        watch_hits: 0,
        watch_size: usize::MAX,
        sizes: [0; SIZE_SLOTS],
        size_counts: [0; SIZE_SLOTS],
        sizes_len: 0,
        sizes_overflowed: false,
        armed: false,
    };

    fn record_alloc(&mut self, size: usize) {
        self.allocs += 1;
        self.bytes += size;
        if size == self.watch_size {
            self.watch_hits += 1;
        }
        for i in 0..self.sizes_len {
            if self.sizes[i] == size {
                self.size_counts[i] += 1;
                return;
            }
        }
        if self.sizes_len < SIZE_SLOTS {
            self.sizes[self.sizes_len] = size;
            self.size_counts[self.sizes_len] = 1;
            self.sizes_len += 1;
        } else {
            self.sizes_overflowed = true;
        }
    }

    /// The sizes seen and their multiplicities, largest count first is *not*
    /// imposed — first-seen order is kept because for a `Vec` doubling chain
    /// that order is the story.
    pub fn size_histogram(&self) -> Vec<(usize, usize)> {
        (0..self.sizes_len)
            .map(|i| (self.sizes[i], self.size_counts[i]))
            .collect()
    }
}

thread_local! {
    static COUNTS: Cell<Counts> = const { Cell::new(Counts::ZERO) };
}

pub struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        note_alloc(layout.size());
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        note_alloc(layout.size());
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        note_dealloc();
        unsafe { System.dealloc(ptr, layout) }
    }

    // Counted explicitly rather than left to the default alloc-copy-dealloc
    // implementation, so that a `Vec` growing in place still shows up as one
    // allocation of the new size and one release of the old.
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        note_alloc(new_size);
        note_dealloc();
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

fn note_alloc(size: usize) {
    COUNTS.with(|c| {
        let mut v = c.get();
        if v.armed {
            v.record_alloc(size);
            c.set(v);
        }
    });
}

fn note_dealloc() {
    COUNTS.with(|c| {
        let mut v = c.get();
        if v.armed {
            v.deallocs += 1;
            c.set(v);
        }
    });
}

/// Run `f` with the counters armed on this thread, and hand back what it
/// returned alongside what it allocated.
///
/// `watch_size` is the allocation size to single out — pass
/// `size_of::<AList<T>>()` to count bucket nodes.
///
/// Nothing inside `f` may allocate on another thread, and `f` should be a tight
/// call: anything the test itself does while the counters are armed is counted.
pub fn measure<R>(watch_size: usize, f: impl FnOnce() -> R) -> (R, Counts) {
    COUNTS.with(|c| {
        let mut v = Counts::ZERO;
        v.watch_size = watch_size;
        v.armed = true;
        c.set(v);
    });
    let r = f();
    let counts = COUNTS.with(|c| {
        let mut v = c.get();
        v.armed = false;
        c.set(Counts::ZERO);
        v
    });
    (r, counts)
}
