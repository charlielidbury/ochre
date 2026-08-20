//! Measurement harness for the two resize strategies.
//!
//! - [`baseline`] is `competitors/aeneas-hashmap/current/hashmap.rs`, the
//!   vendored upstream file, included unmodified. Its resize re-inserts every
//!   entry, allocating a fresh `Box` per moved entry.
//! - [`splice`] is `competitors/aeneas-hashmap/splice/hashmap.rs`, identical
//!   except for `move_elements_from_list`, which relinks nodes instead.
//!
//! The crate installs a counting [`global_allocator`](counting_alloc), so the
//! difference is a measured number rather than a claim about the source shape.

#[path = "../../current/hashmap.rs"]
pub mod baseline;

#[path = "../../splice/hashmap.rs"]
pub mod splice;

pub mod counting_alloc;
pub mod testkit;

#[global_allocator]
static GLOBAL: counting_alloc::Counting = counting_alloc::Counting;
