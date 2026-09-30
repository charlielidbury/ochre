import Mathlib

/-!
# A fixed-capacity hash map with separate chaining, as pure functions

Keys are words; values have an arbitrary type `V`.

Read ASSIGNMENT.md first. Every FIXED region (from a begin-marker comment to the
matching end-marker comment) must stay byte-for-byte as it is. Replace every
`sorry`. You may add definitions and lemmas anywhere outside the FIXED regions.
-/

namespace Bench

-- FIXED-BEGIN repr
/-- A bucket: a singly linked list of (key, value) entries. -/
abbrev Bucket (V : Type) := List (UInt64 × V)

/-- The map, from word keys to values of type `V`. `slots.size` is the
capacity; it is chosen by `new` and never changes. `len` is the number of keys
in the map; `HashMap.len` is also the `len` operation of the specification. -/
structure HashMap (V : Type) where
  slots : Array (Bucket V)
  len : UInt64

namespace HashMap

variable {V : Type}

/-- The index of the bucket of key `k`: `k mod capacity`. It is the only hash
function. -/
def idx (m : HashMap V) (k : UInt64) : Nat :=
  k.toNat % m.slots.size
-- FIXED-END repr

-- FIXED-BEGIN new
/-- An empty map with `cap` empty buckets and `len = 0`. Requires `cap ≥ 1`. -/
def new (cap : UInt64) : HashMap V :=
-- FIXED-END new
  sorry

-- FIXED-BEGIN get
/-- `some v` if `k` is bound to `v`, and `none` otherwise. -/
def get (m : HashMap V) (k : UInt64) : Option V :=
-- FIXED-END get
  sorry

-- FIXED-BEGIN insert
/-- Binds `k` to `v`. Returns the new map and the value `k` was bound to
before, or `none`. -/
def insert (m : HashMap V) (k : UInt64) (v : V) : HashMap V × Option V :=
-- FIXED-END insert
  sorry

-- FIXED-BEGIN remove
/-- Unbinds `k`. Returns the new map and the value `k` was bound to, or
`none`. -/
def remove (m : HashMap V) (k : UInt64) : HashMap V × Option V :=
-- FIXED-END remove
  sorry

-- FIXED-BEGIN modify
/-- The pure counterpart of `*get_mut(m, k) = w`: the map with `w` written into
the entry of `k`, found by walking down the bucket of `k`. Requires `k` to be
present (`m.get k ≠ none`); what it returns when `k` is absent is up to you. -/
def modify (m : HashMap V) (k : UInt64) (w : V) : HashMap V :=
-- FIXED-END modify
  sorry

-- FIXED-BEGIN Inv
/-- The invariant: any predicate you like that makes the properties below
provable. -/
def Inv (m : HashMap V) : Prop :=
-- FIXED-END Inv
  sorry

/-! ## Properties (see ASSIGNMENT.md)

Every property that runs `insert` assumes `m.len.toNat < 2 ^ 64 - 1`. Where a property does arithmetic on
lengths (H12, H13), it does it in `ℕ`, through `UInt64.toNat`. -/

-- FIXED-BEGIN H1
/-- H1. -/
theorem inv_new : ∀ {V : Type} (c : UInt64), 1 ≤ c → Inv (new c : HashMap V) :=
-- FIXED-END H1
  sorry

-- FIXED-BEGIN H2
/-- H2. -/
theorem inv_insert : ∀ {V : Type} (m : HashMap V) (k : UInt64) (v : V),
    Inv m → m.len.toNat < 2 ^ 64 - 1 → Inv (m.insert k v).1 :=
-- FIXED-END H2
  sorry

-- FIXED-BEGIN H3
/-- H3. -/
theorem inv_remove : ∀ {V : Type} (m : HashMap V) (k : UInt64),
    Inv m → Inv (m.remove k).1 :=
-- FIXED-END H3
  sorry

-- FIXED-BEGIN H4
/-- H4. -/
theorem get_new : ∀ {V : Type} (c k : UInt64), 1 ≤ c → (new c : HashMap V).get k = none :=
-- FIXED-END H4
  sorry

-- FIXED-BEGIN H5
/-- H5. -/
theorem get_insert_self : ∀ {V : Type} (m : HashMap V) (k : UInt64) (v : V),
    Inv m → m.len.toNat < 2 ^ 64 - 1 → (m.insert k v).1.get k = some v :=
-- FIXED-END H5
  sorry

-- FIXED-BEGIN H6
/-- H6. -/
theorem get_insert_ne : ∀ {V : Type} (m : HashMap V) (k k' : UInt64) (v : V),
    Inv m → m.len.toNat < 2 ^ 64 - 1 → k' ≠ k → (m.insert k v).1.get k' = m.get k' :=
-- FIXED-END H6
  sorry

-- FIXED-BEGIN H7
/-- H7. -/
theorem insert_result : ∀ {V : Type} (m : HashMap V) (k : UInt64) (v : V),
    Inv m → m.len.toNat < 2 ^ 64 - 1 → (m.insert k v).2 = m.get k :=
-- FIXED-END H7
  sorry

-- FIXED-BEGIN H8
/-- H8. -/
theorem get_remove_self : ∀ {V : Type} (m : HashMap V) (k : UInt64),
    Inv m → (m.remove k).1.get k = none :=
-- FIXED-END H8
  sorry

-- FIXED-BEGIN H9
/-- H9. -/
theorem get_remove_ne : ∀ {V : Type} (m : HashMap V) (k k' : UInt64),
    Inv m → k' ≠ k → (m.remove k).1.get k' = m.get k' :=
-- FIXED-END H9
  sorry

-- FIXED-BEGIN H10
/-- H10. -/
theorem remove_result : ∀ {V : Type} (m : HashMap V) (k : UInt64),
    Inv m → (m.remove k).2 = m.get k :=
-- FIXED-END H10
  sorry

-- FIXED-BEGIN H11
/-- H11. -/
theorem len_new : ∀ {V : Type} (c : UInt64), 1 ≤ c → (new c : HashMap V).len = 0 :=
-- FIXED-END H11
  sorry

-- FIXED-BEGIN H12
/-- H12. -/
theorem len_insert : ∀ {V : Type} (m : HashMap V) (k : UInt64) (v : V),
    Inv m → m.len.toNat < 2 ^ 64 - 1 →
    (m.insert k v).1.len.toNat = if m.get k = none then m.len.toNat + 1 else m.len.toNat :=
-- FIXED-END H12
  sorry

-- FIXED-BEGIN H13
/-- H13. -/
theorem len_remove : ∀ {V : Type} (m : HashMap V) (k : UInt64),
    Inv m →
    (m.remove k).1.len.toNat = if m.get k ≠ none then m.len.toNat - 1 else m.len.toNat :=
-- FIXED-END H13
  sorry

-- FIXED-BEGIN H14
/-- H14. -/
theorem get_modify : ∀ {V : Type} (m : HashMap V) (k k' : UInt64) (w : V),
    Inv m → m.len.toNat < 2 ^ 64 - 1 → m.get k ≠ none →
    (m.modify k w).get k' = (m.insert k w).1.get k' :=
-- FIXED-END H14
  sorry

-- FIXED-BEGIN H15
/-- H15. -/
theorem len_modify : ∀ {V : Type} (m : HashMap V) (k : UInt64) (w : V),
    Inv m → m.len.toNat < 2 ^ 64 - 1 → m.get k ≠ none →
    (m.modify k w).len = (m.insert k w).1.len :=
-- FIXED-END H15
  sorry

-- FIXED-BEGIN H16
/-- H16. -/
theorem inv_modify : ∀ {V : Type} (m : HashMap V) (k : UInt64) (w : V),
    Inv m → m.len.toNat < 2 ^ 64 - 1 → m.get k ≠ none →
    Inv (m.modify k w) :=
-- FIXED-END H16
  sorry

-- FIXED-BEGIN end
end HashMap

end Bench
-- FIXED-END end
