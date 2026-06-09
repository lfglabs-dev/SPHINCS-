/-
  ClimbStepSpec — spec-side single-step unfold lemmas for the two fuel-bounded
  climbs (`xmssClimb`, `forsClimb`) in `C13Concrete`.

  These name the *step combine* function each climb applies per iteration
  (`xmssClimbStep`/`forsClimbStep`) and prove the fuel-`succ` unfold
  (`xmssClimb_succ`/`forsClimb_succ`).  They are the inductive anchors for the open
  Phase-3b data correspondence: the interpreter's `merkleClimbBody` (ClimbKit) writes
  `nodeVar := (keccak 0x00 0x80) & N_MASK` over the branchless-swapped scratch
  `[seed, adrs, child0, child1]`, which is exactly `xmssClimbStep`'s
  `maskN (keccakWords [seed, adrs, node, sibling])` (even) / `[…, sibling, node]`
  (odd).  Matching one interpreter `stepMerkle` to one `xmssClimbStep` — then folding
  by induction on fuel — is the remaining keccak data correspondence.  This file does
  the spec half of the step structure; it asserts nothing about the interpreter and
  evaluates no keccak.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.ClimbStepSpec

open SphincsMinusVerifierSpec (Bytes)
open SphincsMinusVerifierSpec.C13Concrete

set_option maxRecDepth 4000

/-! ## 1. XMSS (hypertree) climb step. -/

/-- One spec XMSS-climb combine: hash `node` with `sibling` under the level-`h+1`
tree address, branchless-swapped by `mIdx`'s parity — left child when even, right
when odd.  This is the exact spec shape the interpreter's `merkleClimbBody`
realises (the `0x40^s`/`0x60^s` swap with `s = (idx & 1) << 5`). -/
def xmssClimbStep (seed treeAdrs : Word) (h mIdx : Nat) (node sibling : Word) : Word :=
  let parentIdx := mIdx / 2
  let adrs := treeAdrs ||| ((h + 1) <<< 32) ||| parentIdx
  if mIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
  else maskN (keccakWords [seed, adrs, sibling, node])

/-- The `h`-th XMSS auth sibling word (spec source: the auth-path byte list). -/
def xmssSibling (auth : List Bytes) (h : Nat) : Word :=
  wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)

/-- **`xmssClimb_succ`** — the spec `xmssClimb` unfolds one fuel step into a single
`xmssClimbStep` applied to the `h`-th sibling, recursing on `fuel`, `h+1`, and the
halved index.  Pure `rfl` against `xmssClimb`'s `succ` branch.  This is the spec-side
induction anchor: a per-step interpreter↔spec match on `xmssClimbStep` folds through
this equation. -/
theorem xmssClimb_succ (seed treeAdrs : Word) (fuel h mIdx : Nat)
    (node : Word) (auth : List Bytes) :
    xmssClimb seed treeAdrs (fuel + 1) h mIdx node auth
      = xmssClimb seed treeAdrs fuel (h + 1) (mIdx / 2)
          (xmssClimbStep seed treeAdrs h mIdx node (xmssSibling auth h)) auth := by
  simp only [xmssClimb, xmssClimbStep, xmssSibling]

/-- The spec climb on zero fuel is the identity (the climb output is the node). -/
theorem xmssClimb_zero (seed treeAdrs : Word) (h mIdx : Nat)
    (node : Word) (auth : List Bytes) :
    xmssClimb seed treeAdrs 0 h mIdx node auth = node := by
  simp only [xmssClimb]

/-! ## 2. FORS climb step. -/

/-- One spec FORS-climb combine: same branchless-swap shape as `xmssClimbStep`, but
under the FORS-tree address `adrsForsNode i h parentIdx`. -/
def forsClimbStep (seed i : Word) (h pathIdx : Nat) (node sibling : Word) : Word :=
  let parentIdx := pathIdx / 2
  let adrs := adrsForsNode i h parentIdx
  if pathIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
  else maskN (keccakWords [seed, adrs, sibling, node])

/-- The `h`-th FORS auth sibling word. -/
def forsSibling (auth : List Bytes) (h : Nat) : Word :=
  wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)

/-- **`forsClimb_succ`** — the spec `forsClimb` unfolds one fuel step into a single
`forsClimbStep`.  Pure `rfl` against `forsClimb`'s `succ` branch. -/
theorem forsClimb_succ (seed i : Word) (fuel h pathIdx : Nat)
    (node : Word) (auth : List Bytes) :
    forsClimb seed i (fuel + 1) h pathIdx node auth
      = forsClimb seed i fuel (h + 1) (pathIdx / 2)
          (forsClimbStep seed i h pathIdx node (forsSibling auth h)) auth := by
  simp only [forsClimb, forsClimbStep, forsSibling]

/-- The spec FORS climb on zero fuel is the identity. -/
theorem forsClimb_zero (seed i : Word) (h pathIdx : Nat)
    (node : Word) (auth : List Bytes) :
    forsClimb seed i 0 h pathIdx node auth = node := by
  simp only [forsClimb]

/-! ## 3. FORS climb as an XMSS-shaped climb.

The interpreter-side Merkle loop is generic in an address base.  FORS supplies the
base `(3 <<< 96) ||| (i <<< 64)` and then uses the same level/index suffix as the
XMSS climb.  These lemmas expose that spec-side correspondence without mentioning
the interpreter. -/

/-- The generic Merkle address built from the FORS tree base is definitionally the
FORS node address, up to `Nat.lor` associativity. -/
theorem forsTreeBase_node_address (i h parentIdx : Nat) :
    (((3 <<< 96) ||| (i <<< 64)) ||| ((h + 1) <<< 32)) ||| parentIdx
      = adrsForsNode i h parentIdx := by
  simp only [adrsForsNode]

/-- FORS climb is the generic XMSS-shaped climb instantiated with the FORS tree
base `(3 <<< 96) ||| (i <<< 64)`. -/
theorem forsClimb_eq_xmssClimb (seed i : Word) (fuel h pathIdx : Nat)
    (node : Word) (auth : List Bytes) :
    forsClimb seed i fuel h pathIdx node auth
      = xmssClimb seed ((3 <<< 96) ||| (i <<< 64)) fuel h pathIdx node auth := by
  induction fuel generalizing h pathIdx node with
  | zero =>
      simp only [forsClimb, xmssClimb]
  | succ fuel ih =>
      simp only [forsClimb, xmssClimb]
      rw [forsTreeBase_node_address]
      exact ih (h + 1) (pathIdx / 2) _

/-! ## 4. Axiom audit. -/

#print axioms xmssClimb_succ
#print axioms xmssClimb_zero
#print axioms forsClimb_succ
#print axioms forsClimb_zero
#print axioms forsTreeBase_node_address
#print axioms forsClimb_eq_xmssClimb

end SphincsMinusVerifiers.ClimbStepSpec
