//! Unverified reference for ../SPEC.md: a fixed-capacity hash map with separate
//! chaining, in place. It exists only to validate tests.json; it is never copied
//! into a sandbox. Recursive, like the packages' likely solutions, and written
//! against exactly the SPEC's representation and API.

/// A bucket: a singly linked list of (key, value) entries (SPEC §2).
pub enum Bucket {
    Nil,
    Cons(u64, u64, Box<Bucket>),
}

/// `slots.len()` is the capacity; it never changes after `new`.
pub struct HashMap {
    slots: Vec<Bucket>,
    len: u64,
}

impl HashMap {
    fn idx(&self, k: u64) -> usize {
        (k % self.slots.len() as u64) as usize
    }

    /// Requires `cap >= 1`.
    pub fn new(cap: u64) -> HashMap {
        assert!(cap >= 1, "new: capacity must be at least 1");
        HashMap { slots: (0..cap).map(|_| Bucket::Nil).collect(), len: 0 }
    }

    pub fn len(&self) -> u64 {
        self.len
    }

    pub fn get(&self, k: u64) -> Option<u64> {
        fn go(b: &Bucket, k: u64) -> Option<u64> {
            match b {
                Bucket::Nil => None,
                Bucket::Cons(key, value, next) => if *key == k { Some(*value) } else { go(next, k) },
            }
        }
        go(&self.slots[self.idx(k)], k)
    }

    pub fn insert(&mut self, k: u64, v: u64) -> Option<u64> {
        // Overwrite in place if present; otherwise append a node at the end.
        fn go(b: &mut Bucket, k: u64, v: u64) -> Option<u64> {
            match b {
                Bucket::Nil => {
                    *b = Bucket::Cons(k, v, Box::new(Bucket::Nil));
                    None
                }
                Bucket::Cons(key, value, next) => {
                    if *key == k { Some(std::mem::replace(value, v)) } else { go(next, k, v) }
                }
            }
        }
        let i = self.idx(k);
        let old = go(&mut self.slots[i], k, v);
        if old.is_none() {
            self.len += 1;
        }
        old
    }

    pub fn remove(&mut self, k: u64) -> Option<u64> {
        // Unlink the node in place: its successor takes its place.
        fn go(b: &mut Bucket, k: u64) -> Option<u64> {
            match b {
                Bucket::Nil => None,
                Bucket::Cons(key, _, next) if *key != k => go(next, k),
                Bucket::Cons(..) => match std::mem::replace(b, Bucket::Nil) {
                    Bucket::Cons(_, value, next) => {
                        *b = *next;
                        Some(value)
                    }
                    Bucket::Nil => unreachable!(),
                },
            }
        }
        let i = self.idx(k);
        let old = go(&mut self.slots[i], k);
        if old.is_some() {
            self.len -= 1;
        }
        old
    }

    /// Requires `self.get(k) != None`.
    pub fn get_mut(&mut self, k: u64) -> &mut u64 {
        fn go(b: &mut Bucket, k: u64) -> &mut u64 {
            match b {
                Bucket::Nil => panic!("get_mut: key {k} is absent"),
                Bucket::Cons(key, value, next) => if *key == k { value } else { go(next, k) },
            }
        }
        let i = self.idx(k);
        go(&mut self.slots[i], k)
    }
}
