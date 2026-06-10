/-
  SegmentS4ForsMerkleFrame — lightweight adapters connecting the S4 FORS inner
  climb statement to the generic Merkle memory-frame loop adapters.

  This file intentionally sits outside `SegmentS4Fors`: it imports the heavier
  `ClimbMemFrameMerkle` module without adding that import to the core S4 segment
  module.  The lemmas here are standalone bridge bricks; they do not touch
  `execC13` or `c13_refines_byte_spec`.
-/

import SphincsMinusVerifiers.SegmentS4Fors
import SphincsMinusVerifiers.ClimbMemFrameMerkle

namespace SphincsMinusVerifiers.SegmentS4ForsMerkleFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbKit (stepMerkle)
open SphincsMinusVerifierSpec.C13Concrete (adrsForsLeaf maskN keccakWords wordOfHash16)

/-- Frozen C13 FORS Merkle-site facts for one outer tree `t`: static
selector/calldata, fixed auth pointer, a bounded ADRS-base witness, and bounded
moving `pathIdx`. -/
def ForsFrozenSite
    (t : Nat) (pkSeed pkRoot message sig : ByteArray) (s : RuntimeState) : Prop :=
  ∃ base,
    s.selector = 0 ∧
    s.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
    lookupValue s.bindings "authPtr"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
    lookupValue s.bindings "forsBase" = base ∧
    base < 2 ^ 256 ∧
    lookupValue s.bindings "pathIdx" < 2 ^ 256

/-- S4-shaped local `stepMerkle` seed-cell frame.  For the actual FORS inner-climb
variable names, the pure local eval facts and parity-swapped child offsets are
discharged here; callers only supply the site-specific masked sibling calldata
read (`h1`) and address assembly eval (`h3`). -/
theorem stepMerkle_preserves_seed_slot_of_s4_eval
    (s : RuntimeState) (idx mIdx vsib vadr : Nat)
    (hpath : lookupValue s.bindings "pathIdx" = mIdx)
    (hmlt : mIdx < 2 ^ 256)
    (h1 : evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib)
    (h3 : evalExpr []
            { s with bindings :=
              (bindValue
                (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
                "parentIdx" (mIdx >>> 1)) }
            (.bitOr (.localVar "forsBase")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr) :
    ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "node"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hpathH : lookupValue stH.bindings "pathIdx" = mIdx := by
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "pathIdx" (wordNormalize idx) (by decide)]
    exact hpath
  have hpath1 : lookupValue st1.bindings "pathIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "pathIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "pathIdx" st1 mIdx hpath1 hmlt
  have hpath3 : lookupValue st3.bindings "pathIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "pathIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "pathIdx" st3 mIdx hpath3 hmlt
  have hsvalt : sval < 2 ^ 256 := by
    dsimp [sval]
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 : lookupValue st4.bindings "s" = sval := by
    dsimp [st4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have h5off : evalExpr [] st4 (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    dsimp [o5]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st4 0x40 sval hs4 (by decide) hsvalt
  have h5val : evalExpr [] st4 (.localVar "node") = some vnode := by
    rfl
  have hs5 : lookupValue st5.bindings "s" = sval := by
    dsimp [st5]
    exact hs4
  have h6off : evalExpr [] st5 (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    dsimp [o6]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st5 0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr [] st5 (.localVar "sibling") =
      some (lookupValue st5.bindings "sibling") := by
    rfl
  have hpar : mIdx % 2 = 0 ∨ mIdx % 2 = 1 := by
    have hlt : mIdx % 2 < 2 := Nat.mod_lt mIdx (by decide)
    omega
  have hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even mIdx hzero
      have ho5 : o5 = 0x40 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.1
      have ho6 : o6 = 0x60 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.2
      exact ⟨hzero, ho5, ho6⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd mIdx hone
      have ho5 : o5 = 0x60 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.1
      have ho6 : o6 = 0x40 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.2
      exact ⟨hone, ho5, ho6⟩
  change ((stepMerkle "node" "pathIdx" "forsBase" "authPtr" stH).world.memory 0).val
      = (stH.world.memory 0).val
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_mem_zero_val_of_parity
    "node" "pathIdx" "forsBase" "authPtr" stH
    vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
    mIdx hparOff h1 h2 h3 h4 h5off h5val h6off h6val

/-- S4-shaped local `stepMerkle` frame for ordinary FORS root cells.  These root
slots live at `0x80 + 32*j`, so they cannot alias the Merkle scratch cells
`0x20`, `0x40`, or `0x60` used by one branchless climb step. -/
theorem stepMerkle_preserves_root_cell_of_s4_eval
    (s : RuntimeState) (j idx mIdx vsib vadr : Nat)
    (hpath : lookupValue s.bindings "pathIdx" = mIdx)
    (hmlt : mIdx < 2 ^ 256)
    (h1 : evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib)
    (h3 : evalExpr []
            { s with bindings :=
              (bindValue
                (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
                "parentIdx" (mIdx >>> 1)) }
            (.bitOr (.localVar "forsBase")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr) :
    ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
        (0x80 + 32 * j)).val
      = (s.world.memory (0x80 + 32 * j)).val := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "node"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hpathH : lookupValue stH.bindings "pathIdx" = mIdx := by
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "pathIdx" (wordNormalize idx) (by decide)]
    exact hpath
  have hpath1 : lookupValue st1.bindings "pathIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "pathIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "pathIdx" st1 mIdx hpath1 hmlt
  have hpath3 : lookupValue st3.bindings "pathIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "pathIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "pathIdx" st3 mIdx hpath3 hmlt
  have hsvalt : sval < 2 ^ 256 := by
    dsimp [sval]
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 : lookupValue st4.bindings "s" = sval := by
    dsimp [st4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have h5off : evalExpr [] st4 (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    dsimp [o5]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st4 0x40 sval hs4 (by decide) hsvalt
  have h5val : evalExpr [] st4 (.localVar "node") = some vnode := by
    rfl
  have hs5 : lookupValue st5.bindings "s" = sval := by
    dsimp [st5]
    exact hs4
  have h6off : evalExpr [] st5 (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    dsimp [o6]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st5 0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr [] st5 (.localVar "sibling") =
      some (lookupValue st5.bindings "sibling") := by
    rfl
  have hpar : mIdx % 2 = 0 ∨ mIdx % 2 = 1 := by
    have hlt : mIdx % 2 < 2 := Nat.mod_lt mIdx (by decide)
    omega
  have hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even mIdx hzero
      have ho5 : o5 = 0x40 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.1
      have ho6 : o6 = 0x60 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.2
      exact ⟨hzero, ho5, ho6⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd mIdx hone
      have ho5 : o5 = 0x60 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.1
      have ho6 : o6 = 0x40 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.2
      exact ⟨hone, ho5, ho6⟩
  have h20 : 0x80 + 32 * j ≠ 0x20 := by omega
  have ho5 : 0x80 + 32 * j ≠ o5 := by
    rcases hparOff with ⟨_, ho5, _⟩ | ⟨_, ho5, _⟩ <;> rw [ho5] <;> omega
  have ho6 : 0x80 + 32 * j ≠ o6 := by
    rcases hparOff with ⟨_, _, ho6⟩ | ⟨_, _, ho6⟩ <;> rw [ho6] <;> omega
  change ((stepMerkle "node" "pathIdx" "forsBase" "authPtr" stH).world.memory
      (0x80 + 32 * j)).val = (stH.world.memory (0x80 + 32 * j)).val
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_mem_val_of_ne
    "node" "pathIdx" "forsBase" "authPtr" stH
    (0x80 + 32 * j) vsib vpar vadr sval o5 vnode o6
    (lookupValue st5.bindings "sibling")
    h20 ho5 ho6 h1 h2 h3 h4 h5off h5val h6off h6val

/-- S4-shaped local `stepMerkle` frame advance.  This packages the pure
interpreter facts for parent-index, selector, child offsets, local node load, and
sibling reread, leaving only the masked calldata load shape and the indexed
`MerkleClimbData` fact as data premises. -/
theorem stepMerkle_forsFrame_hstep_of_s4_data
    (s : RuntimeState) (idx mIdx node seed treeAdrs merklePtr : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (vsib vadr : Nat)
    (hframe : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed treeAdrs merklePtr s (mIdx, node))
    (hidx : idx < 19)
    (hmlt : mIdx < 2 ^ 256)
    (htreeAdrsLt : treeAdrs < 2 ^ 256)
    (hload : vsib = maskN (cdAt idx))
    (hdata : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx)
    (h1 : evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib)
    (h3 : evalExpr []
            { s with bindings :=
              (bindValue
                (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
                "parentIdx" (mIdx >>> 1)) }
            (.bitOr (.localVar "forsBase")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed treeAdrs merklePtr
      (stepMerkle "node" "pathIdx" "forsBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
        seed treeAdrs auth idx (mIdx, node)) := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "node"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hpath : lookupValue s.bindings "pathIdx" = mIdx :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.idx hframe.1
  have hpathH : lookupValue stH.bindings "pathIdx" = mIdx := by
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "pathIdx" (wordNormalize idx) (by decide)]
    exact hpath
  have hpath1 : lookupValue st1.bindings "pathIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "pathIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "pathIdx" st1 mIdx hpath1 hmlt
  have hpath3 : lookupValue st3.bindings "pathIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "pathIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "pathIdx" st3 mIdx hpath3 hmlt
  have hsvalt : sval < 2 ^ 256 := by
    dsimp [sval]
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 : lookupValue st4.bindings "s" = sval := by
    dsimp [st4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have h5off : evalExpr [] st4 (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    dsimp [o5]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st4 0x40 sval hs4 (by decide) hsvalt
  have h5val : evalExpr [] st4 (.localVar "node") = some vnode := by
    rfl
  have hs5 : lookupValue st5.bindings "s" = sval := by
    dsimp [st5]
    exact hs4
  have h6off : evalExpr [] st5 (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    dsimp [o6]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st5 0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr [] st5 (.localVar "sibling") = some vsib := by
    show some (lookupValue st5.bindings "sibling") = some vsib
    dsimp [st5, st4, st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
      "s" "sibling" sval (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "sibling" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hpar : mIdx % 2 = 0 ∨ mIdx % 2 = 1 := by
    have hlt : mIdx % 2 < 2 := Nat.mod_lt mIdx (by decide)
    omega
  have hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even mIdx hzero
      have ho5 : o5 = 0x40 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.1
      have ho6 : o6 = 0x60 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.2
      exact ⟨hzero, ho5, ho6⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd mIdx hone
      have ho5 : o5 = 0x60 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.1
      have ho6 : o6 = 0x40 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.2
      exact ⟨hone, ho5, ho6⟩
  have hvpar : vpar = mIdx / 2 := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.parentIdx_shiftRight mIdx
  have hnode : wordNormalize vnode = node := by
    dsimp [vnode, st4, st3, st2, st1, stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
        "parentIdx" vpar) "s" "node" sval (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "node" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx)) "sibling" "node" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "node" (wordNormalize idx) (by decide)]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.node hframe.1
  have hseed : (stH.world.memory 0x00).val = seed := by
    dsimp [stH]
    exact hframe.2.2.2.1
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hwordlt : idx + 1 < 2 ^ 256 := by omega
  have hshlt : (idx + 1) <<< 32 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right (2 ^ 32) (Nat.succ_le_of_lt hidx))
      (by decide : 19 * 2 ^ 32 < 2 ^ 256)
  have hplt : vpar < 2 ^ 256 := by
    dsimp [vpar]
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hmlt
  have hbaseEval : evalExpr [] st2 (.localVar "forsBase") = some treeAdrs := by
    show some (lookupValue st2.bindings "forsBase") = some treeAdrs
    dsimp [st2, st1, stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "forsBase" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx)) "sibling" "forsBase" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "forsBase" (wordNormalize idx) (by decide)]
    exact congrArg some hframe.2.1
  have hhEval : evalExpr [] st2 (.localVar "h") = some idx := by
    show some (lookupValue st2.bindings "h") = some idx
    dsimp [st2, st1, stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "h" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx)) "sibling" "h" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have h1Lit : evalExpr [] st2 (.literal 1) = some 1 := by
    show some (wordNormalize 1) = some 1
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hplus : evalExpr [] st2 (.add (.localVar "h") (.literal 1)) = some (idx + 1) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st2 (.localVar "h") (.literal 1) idx 1 hhEval h1Lit hidx256 (by decide) hwordlt
  have h32Lit : evalExpr [] st2 (.literal 32) = some 32 := by
    show some (wordNormalize 32) = some 32
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hsh : evalExpr [] st2
      (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      = some ((idx + 1) <<< 32) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st2 (.literal 32) (.add (.localVar "h") (.literal 1)) 32 (idx + 1)
      h32Lit hplus (by decide) hwordlt hshlt
  have hparentEval : evalExpr [] st2 (.localVar "parentIdx") = some vpar := by
    show some (lookupValue st2.bindings "parentIdx") = some vpar
    dsimp [st2]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hadr : wordNormalize vadr = treeAdrs ||| ((idx + 1) <<< 32) ||| mIdx / 2 := by
    have hraw := SphincsMinusVerifiers.ClimbMemFrameMerkle.address_assembly_eq
      st2 (.localVar "forsBase")
      (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      (.localVar "parentIdx") vadr treeAdrs ((idx + 1) <<< 32) vpar
      h3 hbaseEval hsh hparentEval htreeAdrsLt hshlt hplt
    simpa [hvpar] using hraw
  have hsib : wordNormalize vsib = wordOfHash16 ((auth[idx]?).getD ⟨#[]⟩) := by
    rw [hload, SphincsMinusVerifiers.ClimbMemFrameMerkle.wordNormalize_maskN]
    exact hdata
  have hstepData :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations
        stH vadr vsib seed treeAdrs idx mIdx auth :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations.intro
      hseed hadr hsib
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame_hstep
    "node" "pathIdx" "forsBase" "authPtr"
    pkSeed pkRoot message sig seed treeAdrs merklePtr
    s mIdx node idx auth vsib vpar vadr sval o5 vnode o6 vsib
    hframe hparOff hvpar hnode hstepData h1 h2 h3 h4 h5off h5val h6off h6val

/-- S4-shaped bounded-index adapter for the FORS inner Merkle climb: if each
`stepMerkle` iteration preserves `mem[0x00]` after the loop binds the concrete
height to `"h"`, then the whole `forsLeafInnerStmt` preserves the seed cell. -/
theorem forsLeafInner_preserves_seed_slot_bound_of_step
    (hstep : ∀ (s : RuntimeState) (idx : Nat),
      ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_bound
      "node" "pathIdx" "forsBase" "authPtr" 0 19 hstep st s'
      (by simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt] using h)

/-- S4-shaped bounded-index adapter for arbitrary memory cells through the FORS
inner Merkle climb.  This is the ordinary-root analogue of
`forsLeafInner_preserves_seed_slot_bound_of_step`; callers provide the one-step
non-alias frame for the concrete address they are carrying. -/
theorem forsLeafInner_preserves_memory_val_bound_of_step
    (addr : Nat)
    (hstep : ∀ (s : RuntimeState) (idx : Nat),
      ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_bound
      "node" "pathIdx" "forsBase" "authPtr" addr 19 hstep st s'
      (by simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt] using h)

/-- Range-gated memory-frame variant for the FORS inner Merkle climb. -/
theorem forsLeafInner_preserves_memory_val_range_of_step
    (addr : Nat) (D : Nat → Prop)
    (hstep : ∀ (s : RuntimeState) (idx : Nat), D idx →
      ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 19 → D i)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_range
      "node" "pathIdx" "forsBase" "authPtr" addr 19 D hstep st s' hD
      (by simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt] using h)

/-- One FORS leaf iteration preserves every other ordinary root slot, provided
the inner Merkle step frame preserves that slot at each Merkle height.  Together
with `forsLeafStep_root_cell_range`, this supplies the local write/carry split
needed for the six normal FORS root cells. -/
theorem forsLeafStep_preserves_root_cell_range_ne_of_inner_step
    (st : RuntimeState) (j idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx) (hne : j ≠ idx)
    (hstep : ∀ (s : RuntimeState) (h : Nat),
      ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize h) }).world.memory
            (0x80 + 32 * j)).val =
        (s.world.memory (0x80 + 32 * j)).val) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory
        (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val := by
  exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_root_cell_range_ne_of_inner
    st j idx hidx hi hne
    (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_root_cell_range st j)
    (forsLeafInner_preserves_memory_val_bound_of_step (0x80 + 32 * j) hstep)

/-- One FORS leaf iteration preserves every other ordinary root slot when the
inner Merkle steps satisfy the S4-shaped site eval facts.  This is the root-cell
analogue of the seed-cell `*_of_s4_eval` adapters. -/
theorem forsLeafStep_preserves_root_cell_range_ne_of_s4_eval
    (st : RuntimeState) (j idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx) (hne : j ≠ idx)
    (hsite : ∀ (s : RuntimeState) (hidx : Nat),
      ∃ vsib vadr,
        lookupValue s.bindings "pathIdx" < 2 ^ 256 ∧
        evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib ∧
        evalExpr []
            { s with bindings :=
              (bindValue
                (bindValue (bindValue s.bindings "h" (wordNormalize hidx)) "sibling" vsib)
                "parentIdx" (lookupValue s.bindings "pathIdx" >>> 1)) }
            (.bitOr (.localVar "forsBase")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory
        (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val :=
  forsLeafStep_preserves_root_cell_range_ne_of_inner_step st j idx hidx hi hne
    (fun s hidx => by
      rcases hsite s hidx with ⟨vsib, vadr, hlt, h1, h3⟩
      exact stepMerkle_preserves_root_cell_of_s4_eval
        s j hidx (lookupValue s.bindings "pathIdx") vsib vadr rfl hlt h1 h3)

/-- Outer FORS carry for an ordinary root cell, with the suffix-preservation
premise discharged from S4-shaped Merkle site eval facts.  The remaining
ordinary-root data obligation is to identify the iteration-local post-inner
`"node"` with `forsAllRootsC13[j]`. -/
theorem forsOuter_root_cell_eq_iteration_node_of_s4_eval
    (st : RuntimeState) (j : Nat) (hj : j < 6)
    (hsite : ∀ (s : RuntimeState) (hidx : Nat),
      ∃ vsib vadr,
        lookupValue s.bindings "pathIdx" < 2 ^ 256 ∧
        evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib ∧
        evalExpr []
            { s with bindings :=
              (bindValue
                (bindValue (bindValue s.bindings "h" (wordNormalize hidx)) "sibling" vsib)
                "parentIdx" (lookupValue s.bindings "pathIdx" >>> 1)) }
            (.bitOr (.localVar "forsBase")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
        0 (wordNormalize 6)).world.memory (0x80 + 32 * j)).val =
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              { (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                  { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                      { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") := by
  exact SphincsMinusVerifiers.SegmentS4Fors.forsOuter_root_cell_eq_iteration_node_of_suffix_preserves
    st j hj
    (fun s idx hgt hlt => by
      have hi : lookupValue (bindValue s.bindings "i" (wordNormalize idx)) "i" = idx := by
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (lt_trans hlt (by decide))]
      exact forsLeafStep_preserves_root_cell_range_ne_of_s4_eval
        { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
        j idx hlt hi (by omega) hsite)

/-- Inner-climb seed-cell frame reduced to the two site-specific eval facts left
by `stepMerkle_preserves_seed_slot_of_s4_eval`, packaged existentially per
executed Merkle height. -/
theorem forsLeafInner_preserves_seed_slot_bound_of_s4_eval
    (hsite : ∀ (s : RuntimeState) (idx : Nat),
      ∃ vsib vadr,
        lookupValue s.bindings "pathIdx" < 2 ^ 256 ∧
        evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib ∧
        evalExpr []
            { s with bindings :=
              (bindValue
                (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
                "parentIdx" (lookupValue s.bindings "pathIdx" >>> 1)) }
            (.bitOr (.localVar "forsBase")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  exact forsLeafInner_preserves_seed_slot_bound_of_step
    (fun s idx => by
      rcases hsite s idx with ⟨vsib, vadr, hlt, h1, h3⟩
      exact stepMerkle_preserves_seed_slot_of_s4_eval
        s idx (lookupValue s.bindings "pathIdx") vsib vadr rfl hlt h1 h3)
    st s' h

/-- S4-shaped address-assembly evaluator for the inner Merkle climb.  Once the
loop has bound `"h"`, stmt 1 has bound `"sibling"`, and stmt 2 has bound
`"parentIdx"`, the stmt-3 ADRS expression evaluates to some word under ordinary
boundedness hypotheses.  This produces the `vadr` witness required by the
`*_of_s4_eval` seed-frame adapters; it intentionally does not identify the word
with the spec ADRS value. -/
theorem s4_address_assembly_eval_exists
    (s : RuntimeState) (idx vsib base : Nat)
    (hbase : lookupValue s.bindings "forsBase" = base)
    (hbaselt : base < 2 ^ 256)
    (hpathlt : lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (hidx : idx < 19) :
    ∃ vadr,
      evalExpr []
          { s with bindings :=
            (bindValue
              (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
              "parentIdx" (lookupValue s.bindings "pathIdx" >>> 1)) }
          (.bitOr (.localVar "forsBase")
            (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
              (.localVar "parentIdx"))) = some vadr := by
  let stA : RuntimeState :=
    { s with bindings :=
      (bindValue
        (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
        "parentIdx" (lookupValue s.bindings "pathIdx" >>> 1)) }
  let p : Nat := lookupValue s.bindings "pathIdx" >>> 1
  let hword : Nat := idx + 1
  let sh : Nat := hword <<< 32
  let inner : Nat := Nat.lor sh p
  let vadr : Nat := Nat.lor base inner
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hwordlt : hword < 2 ^ 256 := by
    dsimp [hword]
    omega
  have hshlt : sh < 2 ^ 256 := by
    dsimp [sh, hword]
    rw [Nat.shiftLeft_eq]
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right (2 ^ 32) (Nat.succ_le_of_lt hidx))
      (by decide : 19 * 2 ^ 32 < 2 ^ 256)
  have hplt : p < 2 ^ 256 := by
    dsimp [p]
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt
      (Nat.div_le_self (lookupValue s.bindings "pathIdx") (2 ^ 1)) hpathlt
  have hbase_eval : evalExpr [] stA (.localVar "forsBase") = some base := by
    show some (lookupValue stA.bindings "forsBase") = some base
    dsimp [stA]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "forsBase" (lookupValue s.bindings "pathIdx" >>> 1) (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx))
      "sibling" "forsBase" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "forsBase" (wordNormalize idx) (by decide)]
    rw [hbase]
  have hh_eval : evalExpr [] stA (.localVar "h") = some idx := by
    show some (lookupValue stA.bindings "h") = some idx
    dsimp [stA]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "h" (lookupValue s.bindings "pathIdx" >>> 1) (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx))
      "sibling" "h" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have hparent_eval : evalExpr [] stA (.localVar "parentIdx") = some p := by
    show some (lookupValue stA.bindings "parentIdx") = some p
    dsimp [stA, p]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hlit1 : evalExpr [] stA (.literal 1) = some 1 := by
    show some (wordNormalize 1) = some 1
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hplus : evalExpr [] stA (.add (.localVar "h") (.literal 1)) = some hword := by
    dsimp [hword]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      stA (.localVar "h") (.literal 1) idx 1 hh_eval hlit1 hidx256 (by decide) hwordlt
  have hlit32 : evalExpr [] stA (.literal 32) = some 32 := by
    show some (wordNormalize 32) = some 32
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hsh : evalExpr [] stA (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      = some sh := by
    dsimp [sh]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      stA (.literal 32) (.add (.localVar "h") (.literal 1)) 32 hword
      hlit32 hplus (by decide) hwordlt hshlt
  have hinner : evalExpr [] stA
      (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
        (.localVar "parentIdx")) = some inner := by
    dsimp [inner]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      stA (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      (.localVar "parentIdx") sh p hsh hparent_eval hshlt hplt
  refine ⟨vadr, ?_⟩
  dsimp [vadr]
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
    stA (.localVar "forsBase")
    (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      (.localVar "parentIdx")) base inner hbase_eval hinner hbaselt
    (Nat.bitwise_lt_two_pow hshlt hplt)

/-- Concrete S4 Merkle-site package from the frozen C13 calldata image.  This
combines the masked sibling calldata read (`h1`) with the local ADRS assembly
eval (`h3`) into the exact existential shape consumed by the S4 seed/root-cell
adapters. -/
theorem s4_eval_site_of_frozen_calldata
    (s : RuntimeState) (idx ap base sOff : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsel : s.selector = 0)
    (hcd : s.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : lookupValue s.bindings "authPtr" = ap)
    (hbase : lookupValue s.bindings "forsBase" = base)
    (hbaselt : base < 2 ^ 256)
    (hpathlt : lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (hidx : idx < 19)
    (haplt : ap < 2 ^ 256)
    (hshift : idx <<< 4 < 2 ^ 256)
    (hsum : ap + idx <<< 4 < 2 ^ 256)
    (hoff : ap + idx <<< 4 = SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff)
    (hoff4 : 4 ≤ SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff) :
    ∃ vsib vadr,
      lookupValue s.bindings "pathIdx" < 2 ^ 256 ∧
      evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
          (.bitAnd (.calldataload (.add (.localVar "authPtr")
            (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
        = some vsib ∧
      evalExpr []
          { s with bindings :=
            (bindValue
              (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
              "parentIdx" (lookupValue s.bindings "pathIdx" >>> 1)) }
          (.bitOr (.localVar "forsBase")
            (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
              (.localVar "parentIdx"))) = some vadr := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vsib : Nat :=
    SphincsMinusVerifierSpec.C13Concrete.maskN
      (Compiler.Proofs.YulGeneration.calldataloadWord 0
        (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
        (SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff))
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hselH : stH.selector = 0 := by
    dsimp [stH]
    exact hsel
  have hcdH : stH.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig := by
    dsimp [stH]
    exact hcd
  have hapH : evalExpr [] stH (.localVar "authPtr") = some ap := by
    show some (lookupValue stH.bindings "authPtr") = some ap
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "authPtr" (wordNormalize idx) (by decide)]
    rw [hap]
  have hhH : evalExpr [] stH (.localVar "h") = some idx := by
    show some (lookupValue stH.bindings "h") = some idx
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have h1 : evalExpr [] stH
        (.bitAnd (.calldataload (.add (.localVar "authPtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      = some vsib := by
    dsimp [vsib]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_sibling_read_frozen
      stH "authPtr" pkSeed pkRoot message sig ap idx sOff
      hselH hcdH hapH hhH haplt hidx256 hshift hsum hoff hoff4
  rcases s4_address_assembly_eval_exists s idx vsib base hbase hbaselt hpathlt hidx with
    ⟨vadr, h3⟩
  exact ⟨vsib, vadr, hpathlt, h1, h3⟩

/-- FORS-specialized frozen-calldata Merkle-site package.  For tree `t < 6`,
the setup-auth pointer is `sigDataOffset + (128 + 304*t)` and height `idx < 19`
reads the auth-path word at byte offset `128 + 304*t + 16*idx` inside the
signature.  This wrapper discharges the fixed C13 offset arithmetic and leaves
callers only the real setup bindings/bounds plus the frozen calldata frame. -/
theorem s4_eval_site_of_fors_frozen_calldata
    (s : RuntimeState) (t idx base : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsel : s.selector = 0)
    (hcd : s.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : lookupValue s.bindings "authPtr"
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t))
    (hbase : lookupValue s.bindings "forsBase" = base)
    (hbaselt : base < 2 ^ 256)
    (hpathlt : lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (ht : t < 6)
    (hidx : idx < 19) :
    ∃ vsib vadr,
      lookupValue s.bindings "pathIdx" < 2 ^ 256 ∧
      evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
          (.bitAnd (.calldataload (.add (.localVar "authPtr")
            (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
        = some vsib ∧
      evalExpr []
          { s with bindings :=
            (bindValue
              (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
              "parentIdx" (lookupValue s.bindings "pathIdx" >>> 1)) }
          (.bitOr (.localVar "forsBase")
            (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
              (.localVar "parentIdx"))) = some vadr := by
  let ap : Nat := SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t)
  let sOff : Nat := 128 + 304 * t + 16 * idx
  have haplt : ap < 2 ^ 256 := by
    dsimp [ap]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset]
    omega
  have hshift : idx <<< 4 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    omega
  have hsum : ap + idx <<< 4 < 2 ^ 256 := by
    dsimp [ap]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset, Nat.shiftLeft_eq]
    omega
  have hoff : ap + idx <<< 4 = SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff := by
    dsimp [ap, sOff]
    rw [Nat.shiftLeft_eq]
    omega
  have hoff4 : 4 ≤ SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff := by
    dsimp [sOff]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset]
    omega
  exact s4_eval_site_of_frozen_calldata s idx ap base sOff pkSeed pkRoot message sig
    hsel hcd hap hbase hbaselt hpathlt hidx haplt hshift hsum hoff hoff4

/-- FORS-specialized local `stepMerkle` frame advance from the frozen C13 calldata
layout.  This pins the statement-1 sibling load to the concrete auth-path
calldata word, assembles the local address word, and delegates the remaining
frame update to `stepMerkle_forsFrame_hstep_of_s4_data`. -/
theorem stepMerkle_forsFrame_hstep_of_fors_frozen_calldata
    (s : RuntimeState) (t idx mIdx node seed treeAdrs : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (auth : List SphincsMinusVerifierSpec.Bytes)
    (hframe : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed treeAdrs
        (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t))
        s (mIdx, node))
    (ht : t < 6)
    (hidx : idx < 19)
    (hmlt : mIdx < 2 ^ 256)
    (htreeAdrsLt : treeAdrs < 2 ^ 256)
    (hdata : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
        (fun h =>
          Compiler.Proofs.YulGeneration.calldataloadWord 0
            (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
            (SphincsMinusVerifiers.MkC13State.sigDataOffset
              + (128 + 304 * t) + 16 * h)) idx) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed treeAdrs
      (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t))
      (stepMerkle "node" "pathIdx" "forsBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
        seed treeAdrs auth idx (mIdx, node)) := by
  let cdAt : Nat → Nat := fun h =>
    Compiler.Proofs.YulGeneration.calldataloadWord 0
      (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
        ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
      (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) + 16 * h)
  let vsib : Nat := SphincsMinusVerifierSpec.C13Concrete.maskN (cdAt idx)
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  have hsel : s.selector = 0 := hframe.2.2.2.2.1
  have hcd : s.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig := hframe.2.2.2.2.2.1
  have hbase : lookupValue s.bindings "forsBase" = treeAdrs := hframe.2.1
  have hap : lookupValue s.bindings "authPtr"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) :=
    hframe.2.2.1
  have hpath : lookupValue s.bindings "pathIdx" = mIdx :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.idx hframe.1
  have hpathlt : lookupValue s.bindings "pathIdx" < 2 ^ 256 := by
    rw [hpath]
    exact hmlt
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  let ap : Nat := SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t)
  let sOff : Nat := 128 + 304 * t + 16 * idx
  have haplt : ap < 2 ^ 256 := by
    dsimp [ap]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset]
    omega
  have hshift : idx <<< 4 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    omega
  have hsum : ap + idx <<< 4 < 2 ^ 256 := by
    dsimp [ap]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset, Nat.shiftLeft_eq]
    omega
  have hoff : ap + idx <<< 4 = SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff := by
    dsimp [ap, sOff]
    rw [Nat.shiftLeft_eq]
    omega
  have hoff4 : 4 ≤ SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff := by
    dsimp [sOff]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset]
    omega
  have hapH : evalExpr [] stH (.localVar "authPtr") = some ap := by
    show some (lookupValue stH.bindings "authPtr") = some ap
    dsimp [stH, ap]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "authPtr" (wordNormalize idx) (by decide)]
    exact congrArg some hap
  have hhH : evalExpr [] stH (.localVar "h") = some idx := by
    show some (lookupValue stH.bindings "h") = some idx
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have h1 : evalExpr [] stH
        (.bitAnd (.calldataload (.add (.localVar "authPtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      = some vsib := by
    have hraw :=
      SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_sibling_read_frozen
      stH "authPtr" pkSeed pkRoot message sig ap idx sOff
      (by dsimp [stH]; exact hsel)
      (by dsimp [stH]; exact hcd)
      hapH hhH haplt hidx256 hshift hsum hoff hoff4
    have hsOff :
        SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff
          = SphincsMinusVerifiers.MkC13State.sigDataOffset
              + (128 + 304 * t) + 16 * idx := by
      dsimp [sOff]
      omega
    rw [hsOff] at hraw
    simpa [vsib, cdAt] using hraw
  rcases s4_address_assembly_eval_exists s idx vsib treeAdrs
      hbase htreeAdrsLt hpathlt hidx with
    ⟨vadr, h3⟩
  have h3m : evalExpr []
        { s with bindings :=
          (bindValue
            (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
            "parentIdx" (mIdx >>> 1)) }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr := by
    simpa [hpath] using h3
  exact stepMerkle_forsFrame_hstep_of_s4_data
    s idx mIdx node seed treeAdrs
    (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t))
    pkSeed pkRoot message sig auth cdAt vsib vadr hframe hidx hmlt htreeAdrsLt
    (by rfl)
    (by simpa [cdAt] using hdata) h1 h3m

/-- Bundle the local `forsLeafSetupStep` facts into the frozen-calldata site
shape consumed by the C13 FORS Merkle frame adapters.  This is still a
single-step setup fact: callers must thread it to the concrete inner states. -/
theorem forsLeafSetupStep_fors_frozen_calldata_site
    (st : RuntimeState) (t : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hi : lookupValue st.bindings "i" = t)
    (ht : t < 6)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig) :
    ∃ base,
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).selector = 0 ∧
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).world.calldata
        = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
            ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings "authPtr"
        = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
        "forsBase" = base ∧
      base < 2 ^ 256 ∧
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
        "pathIdx" < 2 ^ 256 := by
  rcases SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_selector_calldata
      st with ⟨hselStep, hcdStep⟩
  rcases SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_treeAdrsBase_exists_lt
      st t hi with ⟨base, hbase, hbaselt⟩
  refine ⟨base, ?_, ?_, ?_, hbase, hbaselt, ?_⟩
  · rw [hselStep, hsel]
  · rw [hcdStep, hcd]
  · have hsigBase164 : lookupValue st.bindings "sigBase" = 164 := by
      simpa [SphincsMinusVerifiers.MkC13State.sigDataOffset] using hsigBase
    have hap :=
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_authPtr_eq_sigDataOffset
        st t hi hsigBase164 ht
    simpa [SphincsMinusVerifiers.MkC13State.sigDataOffset] using hap
  · exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_pathIdx_lt st t hi

/-- Predicate-form wrapper for the local setup-site package. -/
theorem forsLeafSetupStep_forsFrozenSite
    (st : RuntimeState) (t : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hi : lookupValue st.bindings "i" = t)
    (ht : t < 6)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig) :
    ForsFrozenSite t pkSeed pkRoot message sig
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st) :=
  forsLeafSetupStep_fors_frozen_calldata_site st t pkSeed pkRoot message sig
    hi ht hsigBase hsel hcd

/-- Initial FORS climb relation after the straight-line setup prefix.  The index
component is the decoded `treeIdx`, and the node component is the concrete spec
FORS leaf hash word. -/
theorem forsLeafSetupStep_initial_forsClimbRel_of_eval
    (st : RuntimeState) (seed i treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr
          (.shl (.literal 96) (.literal 3))
          (.bitOr (.shl (.literal 64) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf i treeIdx)) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      (treeIdx, maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) := by
  refine SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.intro ?_ ?_
  · exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_pathIdx_eq_of_eval
      st treeIdx hTree
  · rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_node_eq_spec_of_eval
      st seed i treeIdx sk hm0 hAdrLt hSkLt hTree hSecret hLeaf]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.wordNormalize_maskN _

/-- Initial frame-carrying FORS climb invariant after the straight-line setup.
The relation component comes from the setup evaluator; the static frame comes
from the concrete frozen-site package.  The frame uses the actual post-setup
`"forsBase"`/`"authPtr"` words, avoiding another raw address-arithmetic
obligation at this boundary. -/
theorem forsLeafSetupStep_initial_forsClimbFrame_of_eval_site
    (st : RuntimeState) (seed i treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ForsFrozenSite i pkSeed pkRoot message sig
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr
          (.shl (.literal 96) (.literal 3))
          (.bitOr (.shl (.literal 64) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf i treeIdx)) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed
      (lookupValue
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
        "forsBase")
      (lookupValue
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
        "authPtr")
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      (treeIdx, maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) := by
  rcases hsite with ⟨base, hsel, hcd, _hap, _hbase, _hbaselt, _hpathlt⟩
  refine ⟨?_, rfl, rfl, ?_, hsel, hcd,
    (by decide), (by decide), (by decide), (by decide), (by decide),
    (by decide), (by decide), (by decide), (by decide),
    (by decide), (by decide), (by decide), (by decide), (by decide), (by decide),
    (by decide), (by decide), (by decide), (by decide), (by decide), (by decide)⟩
  · exact forsLeafSetupStep_initial_forsClimbRel_of_eval
      st seed i treeIdx sk hm0 hAdrLt hSkLt hTree hSecret hLeaf
  · rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_seed_slot]
    exact hm0

/-- Conditional post-inner FORS node correspondence for one normal C13 FORS tree.
The straight-line setup supplies the initial `MerkleClimbRel`; callers still own
the per-height Merkle data and relation-step facts for the 19 auth-path levels. -/
theorem forsLeafInnerStep_node_eq_forsClimb_of_eval
    (st : RuntimeState) (seed i treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed ((3 <<< 96) ||| (i <<< 64)) auth idx a))
    (hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr
          (.shl (.literal 96) (.literal 3))
          (.bitOr (.shl (.literal 64) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf i treeIdx)) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings "node")
      =
        SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i 19 0 treeIdx
          (maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) auth := by
  let setup := SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st
  let start : RuntimeState := { setup with bindings := bindValue setup.bindings "h" (wordNormalize 0) }
  have hR0 :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
        setup
        (treeIdx, maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) :=
    forsLeafSetupStep_initial_forsClimbRel_of_eval st seed i treeIdx sk
      hm0 hAdrLt hSkLt hTree hSecret hLeaf
  have hR :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
        start
        (treeIdx, maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) := by
    refine SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.intro ?_ ?_
    · dsimp [start]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        setup.bindings "h" "pathIdx" (wordNormalize 0) (by decide)]
      exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.idx hR0
    · dsimp [start]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        setup.bindings "h" "node" (wordNormalize 0) (by decide)]
      exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.node hR0
  have hmodel :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.forsClimb_model_node
      "node" "pathIdx" "forsBase" "authPtr"
      seed i auth cdAt hstep start treeIdx
      (maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk]))
      0 19 hD hR
  have h19 : wordNormalize 19 = 19 := by
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 19 < 2 ^ 256)]
  unfold SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
  rw [h19]
  exact hmodel

/-- Frame-carrying post-inner FORS node correspondence for one normal C13 FORS
tree.  This is the frame-shaped sibling of
`forsLeafInnerStep_node_eq_forsClimb_of_eval`: setup supplies the initial
`MerkleClimbFrame`, the range-gated setup theorem rewrites `"forsBase"` to
the exact C13 ADRS base, and callers provide the per-height frame step facts. -/
theorem forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site
    (st : RuntimeState) (seed i treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (pkSeed pkRoot message sig : ByteArray)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hi : lookupValue st.bindings "i" = i)
    (hiLt : i < 6)
    (hsite : ForsFrozenSite i pkSeed pkRoot message sig
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "node" "pathIdx" "forsBase" "authPtr"
          pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
          (lookupValue
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
            "authPtr")
          s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "node" "pathIdx" "forsBase" "authPtr"
          pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
          (lookupValue
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
            "authPtr")
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed ((3 <<< 96) ||| (i <<< 64)) auth idx a))
    (hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr
          (.shl (.literal 96) (.literal 3))
          (.bitOr (.shl (.literal 64) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf i treeIdx)) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings "node")
      =
        SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i 19 0 treeIdx
          (maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) auth := by
  let setup := SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st
  let start : RuntimeState := { setup with bindings := bindValue setup.bindings "h" (wordNormalize 0) }
  have hFrame0 :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed
        (lookupValue setup.bindings "forsBase")
        (lookupValue setup.bindings "authPtr")
        setup
        (treeIdx, maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) := by
    simpa [setup] using
      forsLeafSetupStep_initial_forsClimbFrame_of_eval_site
        st seed i treeIdx sk pkSeed pkRoot message sig hsite
        hm0 hAdrLt hSkLt hTree hSecret hLeaf
  have hbase :
      lookupValue setup.bindings "forsBase" = (3 <<< 96) ||| (i <<< 64) := by
    simpa [setup] using
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_treeAdrsBase_eq_of_i
        st i hi hiLt
  have hFrameExact :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
        (lookupValue setup.bindings "authPtr")
        setup
        (treeIdx, maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) := by
    simpa [hbase] using hFrame0
  have hFrameStart :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
        (lookupValue setup.bindings "authPtr")
        start
        (treeIdx, maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame_h_inject
      "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
      (lookupValue setup.bindings "authPtr") setup
      (treeIdx, maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk]))
      (wordNormalize 0) hFrameExact
  have hmodel :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.forsClimbFrame_model_node
      "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed i
      (lookupValue setup.bindings "authPtr") auth cdAt hstep start treeIdx
      (maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk]))
      0 19 hD hFrameStart
  have h19 : wordNormalize 19 = 19 := by
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 19 < 2 ^ 256)]
  unfold SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
  rw [h19]
  exact hmodel

/-- Range-gated sibling of
`forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site`.  The per-height frame
step receives the concrete bound `idx < 19`, so callers can use calldata facts
whose offset arithmetic is only valid over the FORS auth-path range. -/
theorem forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site_range
    (st : RuntimeState) (seed i treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (pkSeed pkRoot message sig : ByteArray)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hi : lookupValue st.bindings "i" = i)
    (hiLt : i < 6)
    (hsite : ForsFrozenSite i pkSeed pkRoot message sig
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat), idx < 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "node" "pathIdx" "forsBase" "authPtr"
          pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
          (lookupValue
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
            "authPtr")
          s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "node" "pathIdx" "forsBase" "authPtr"
          pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
          (lookupValue
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
            "authPtr")
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed ((3 <<< 96) ||| (i <<< 64)) auth idx a))
    (hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr
          (.shl (.literal 96) (.literal 3))
          (.bitOr (.shl (.literal 64) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf i treeIdx)) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings "node")
      =
        SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i 19 0 treeIdx
          (maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) auth := by
  let setup := SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st
  let start : RuntimeState := { setup with bindings := bindValue setup.bindings "h" (wordNormalize 0) }
  let node0 := maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])
  have hFrame0 :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed
        (lookupValue setup.bindings "forsBase")
        (lookupValue setup.bindings "authPtr")
        setup (treeIdx, node0) := by
    simpa [setup, node0] using
      forsLeafSetupStep_initial_forsClimbFrame_of_eval_site
        st seed i treeIdx sk pkSeed pkRoot message sig hsite
        hm0 hAdrLt hSkLt hTree hSecret hLeaf
  have hbase :
      lookupValue setup.bindings "forsBase" = (3 <<< 96) ||| (i <<< 64) := by
    simpa [setup] using
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_treeAdrsBase_eq_of_i
        st i hi hiLt
  have hFrameExact :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
        (lookupValue setup.bindings "authPtr")
        setup (treeIdx, node0) := by
    simpa [hbase] using hFrame0
  have hFrameStart :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
        (lookupValue setup.bindings "authPtr")
        start (treeIdx, node0) :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame_h_inject
      "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
      (lookupValue setup.bindings "authPtr") setup (treeIdx, node0)
      (wordNormalize 0) hFrameExact
  let D : Nat → Prop := fun idx =>
    idx < 19 ∧ SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx
  have hD' : ∀ idx, 0 ≤ idx → idx < 0 + 19 → D idx := by
    intro idx h0 hlt
    exact ⟨by omega, hD idx h0 hlt⟩
  have hframe :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_invariant_cond "h"
      (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
        seed ((3 <<< 96) ||| (i <<< 64)) auth)
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
        (lookupValue setup.bindings "authPtr"))
      D
      (fun s a idx hDi hR => hstep s a idx hDi.1 hDi.2 hR)
      start (treeIdx, node0) 0 19 hD' hFrameStart
  have hnode :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
            start 0 19).bindings "node")
        =
          (SphincsMinusVerifiers.ClimbLoop.specFold
            (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
              seed ((3 <<< 96) ||| (i <<< 64)) auth)
            (treeIdx, node0) 0 19).2 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame.toRel hframe |>.node
  have hx :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
            start 0 19).bindings "node")
        =
          SphincsMinusVerifierSpec.C13Concrete.xmssClimb seed
            ((3 <<< 96) ||| (i <<< 64)) 19 0 treeIdx node0 auth :=
    hnode.trans
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.xmssClimb_eq_specFold
        seed ((3 <<< 96) ||| (i <<< 64)) auth 19 0 treeIdx node0).symm
  have hmodel :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
            start 0 19).bindings "node")
        =
          SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i 19 0 treeIdx node0 auth :=
    hx.trans
      (SphincsMinusVerifiers.ClimbStepSpec.forsClimb_eq_xmssClimb
        seed i 19 0 treeIdx node0 auth).symm
  have h19 : wordNormalize 19 = 19 := by
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 19 < 2 ^ 256)]
  unfold SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
  rw [h19]
  exact hmodel

/-- Range-gated frame-carrying post-inner theorem that also carries the spec-side
path-index word bound through the loop.  This is the shape needed by concrete
calldata step facts, since the local address/shift evaluators require the moving
`pathIdx` to stay below `2^256`. -/
theorem forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site_range_path_bound
    (st : RuntimeState) (seed i treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (pkSeed pkRoot message sig : ByteArray)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hi : lookupValue st.bindings "i" = i)
    (hiLt : i < 6)
    (hTreeIdxLt : treeIdx < 2 ^ 256)
    (hsite : ForsFrozenSite i pkSeed pkRoot message sig
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat), idx < 19 →
        a.1 < 2 ^ 256 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "node" "pathIdx" "forsBase" "authPtr"
          pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
          (lookupValue
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
            "authPtr")
          s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "node" "pathIdx" "forsBase" "authPtr"
          pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
          (lookupValue
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
            "authPtr")
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed ((3 <<< 96) ||| (i <<< 64)) auth idx a))
    (hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr
          (.shl (.literal 96) (.literal 3))
          (.bitOr (.shl (.literal 64) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf i treeIdx)) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings "node")
      =
        SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i 19 0 treeIdx
          (maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) auth := by
  let setup := SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st
  let start : RuntimeState := { setup with bindings := bindValue setup.bindings "h" (wordNormalize 0) }
  let node0 := maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])
  let base := (3 <<< 96) ||| (i <<< 64)
  let merklePtr := lookupValue setup.bindings "authPtr"
  let R : RuntimeState → Nat × Nat → Prop := fun s a =>
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed base merklePtr s a ∧ a.1 < 2 ^ 256
  have hFrame0 :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed
        (lookupValue setup.bindings "forsBase")
        (lookupValue setup.bindings "authPtr")
        setup (treeIdx, node0) := by
    simpa [setup, node0] using
      forsLeafSetupStep_initial_forsClimbFrame_of_eval_site
        st seed i treeIdx sk pkSeed pkRoot message sig hsite
        hm0 hAdrLt hSkLt hTree hSecret hLeaf
  have hbase :
      lookupValue setup.bindings "forsBase" = base := by
    simpa [setup, base] using
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_treeAdrsBase_eq_of_i
        st i hi hiLt
  have hFrameExact :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed base merklePtr
        setup (treeIdx, node0) := by
    simpa [merklePtr, hbase] using hFrame0
  have hFrameStart :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "node" "pathIdx" "forsBase" "authPtr"
        pkSeed pkRoot message sig seed base merklePtr
        start (treeIdx, node0) :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame_h_inject
      "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed base merklePtr setup (treeIdx, node0)
      (wordNormalize 0) hFrameExact
  let D : Nat → Prop := fun idx =>
    idx < 19 ∧ SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx
  have hD' : ∀ idx, 0 ≤ idx → idx < 0 + 19 → D idx := by
    intro idx h0 hlt
    exact ⟨by omega, hD idx h0 hlt⟩
  have hR0 : R start (treeIdx, node0) := by
    exact ⟨hFrameStart, hTreeIdxLt⟩
  have hpair :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_invariant_cond "h"
      (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep seed base auth)
      R D
      (fun s a idx hDi hR => by
        refine ⟨?_, ?_⟩
        · exact hstep s a idx hDi.1 hR.2 hDi.2 hR.1
        · dsimp [SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep]
          exact Nat.lt_of_le_of_lt (Nat.div_le_self a.1 2) hR.2)
      start (treeIdx, node0) 0 19 hD' hR0
  have hnode :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
            start 0 19).bindings "node")
        =
          (SphincsMinusVerifiers.ClimbLoop.specFold
            (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep seed base auth)
            (treeIdx, node0) 0 19).2 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame.toRel hpair.1 |>.node
  have hx :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
            start 0 19).bindings "node")
        =
          SphincsMinusVerifierSpec.C13Concrete.xmssClimb seed base 19 0 treeIdx node0 auth :=
    hnode.trans
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.xmssClimb_eq_specFold
        seed base auth 19 0 treeIdx node0).symm
  have hmodel :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
            start 0 19).bindings "node")
        =
          SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i 19 0 treeIdx node0 auth :=
    hx.trans
      (SphincsMinusVerifiers.ClimbStepSpec.forsClimb_eq_xmssClimb
        seed i 19 0 treeIdx node0 auth).symm
  have h19 : wordNormalize 19 = 19 := by
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 19 < 2 ^ 256)]
  unfold SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
  rw [h19]
  simpa [base, node0] using hmodel

/-- Concrete frozen-calldata post-inner FORS node correspondence.  This closes
the frame-step side of the range/path-bound handoff with
`stepMerkle_forsFrame_hstep_of_fors_frozen_calldata`; callers still provide the
parsed auth-path `MerkleClimbData` range and the straight-line setup eval facts. -/
theorem forsLeafInnerStep_node_eq_forsClimbFrame_of_fors_frozen_calldata
    (st : RuntimeState) (seed i treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (pkSeed pkRoot message sig : ByteArray)
    (auth : List SphincsMinusVerifierSpec.Bytes)
    (hi : lookupValue st.bindings "i" = i)
    (hiLt : i < 6)
    (hTreeIdxLt : treeIdx < 2 ^ 256)
    (hsite : ForsFrozenSite i pkSeed pkRoot message sig
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
    (hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
          (fun h =>
            Compiler.Proofs.YulGeneration.calldataloadWord 0
              (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
              (SphincsMinusVerifiers.MkC13State.sigDataOffset
                + (128 + 304 * i) + 16 * h)) idx)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr
          (.shl (.literal 96) (.literal 3))
          (.bitOr (.shl (.literal 64) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf i treeIdx)) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings "node")
      =
        SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i 19 0 treeIdx
          (maskN (keccakWords [seed, adrsForsLeaf i treeIdx, wordOfHash16 sk])) auth := by
  let setup := SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st
  rcases hsite with ⟨base0, _hsel, _hcd, hap, hbaseSite, hbaselt, _hpathlt⟩
  have hbaseExact :
      lookupValue setup.bindings "forsBase" = (3 <<< 96) ||| (i <<< 64) := by
    simpa [setup] using
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_treeAdrsBase_eq_of_i
        st i hi hiLt
  have htreeAdrsLt : ((3 <<< 96) ||| (i <<< 64)) < 2 ^ 256 := by
    rw [← hbaseExact]
    rw [hbaseSite]
    exact hbaselt
  have hapSetup :
      lookupValue setup.bindings "authPtr"
        = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i) := by
    simpa [setup] using hap
  exact forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site_range_path_bound
    st seed i treeIdx sk pkSeed pkRoot message sig auth
    (fun h =>
      Compiler.Proofs.YulGeneration.calldataloadWord 0
        (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
        (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i) + 16 * h))
    hi hiLt hTreeIdxLt
    (by exact ⟨base0, _hsel, _hcd, hap, hbaseSite, hbaselt, _hpathlt⟩)
    (fun s a idx hidx hmlt hdata hframe => by
      have hframeFixed :
          SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
            "node" "pathIdx" "forsBase" "authPtr"
            pkSeed pkRoot message sig seed ((3 <<< 96) ||| (i <<< 64))
            (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
            s a := by
        simpa [setup, hapSetup] using hframe
      have hnext :=
        stepMerkle_forsFrame_hstep_of_fors_frozen_calldata
          s i idx a.1 a.2 seed ((3 <<< 96) ||| (i <<< 64))
          pkSeed pkRoot message sig auth hframeFixed hiLt hidx hmlt htreeAdrsLt hdata
      simpa [setup, hapSetup] using hnext)
    hD hm0 hAdrLt hSkLt hTree hSecret hLeaf

/-- C13 normal-root form of `forsLeafInnerStep_node_eq_forsClimb_of_eval`.  This
is the exact post-inner `"node"` equality expected by the six normal FORS
root-cell adapters. -/
theorem forsLeafInnerStep_node_eq_forsAllRootsC13_getElem_of_eval
    (st : RuntimeState) (pk : SphincsMinusVerifierSpec.PublicKey)
    (digest : SphincsMinusVerifierSpec.HMsg)
    (fors : SphincsMinusVerifierSpec.ForsSig) (j : Nat) (hj : j < 6)
    (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          ((fors.authPath[j]?).getD []) cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            (wordOfHash16 pk.pkSeed) ((3 <<< 96) ||| (j <<< 64))
            ((fors.authPath[j]?).getD []) idx a))
    (hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          ((fors.authPath[j]?).getD []) cdAt idx)
    (hm0 : (st.world.memory 0).val = wordOfHash16 pk.pkSeed)
    (hAdrLt : adrsForsLeaf j ((digest.forsIndex[j]?).getD 0) < 2 ^ 256)
    (hSkLt : wordOfHash16 ((fors.sk[j]?).getD ⟨#[]⟩) < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some ((digest.forsIndex[j]?).getD 0))
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" ((digest.forsIndex[j]?).getD 0) }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 ((fors.sk[j]?).getD ⟨#[]⟩)))
    (hLeaf : evalExpr []
        { st with bindings :=
            (bindValue
              (bindValue st.bindings "treeIdx" ((digest.forsIndex[j]?).getD 0))
              "secretVal" (wordOfHash16 ((fors.sk[j]?).getD ⟨#[]⟩))) }
        (.bitOr
          (.shl (.literal 96) (.literal 3))
          (.bitOr (.shl (.literal 64) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf j ((digest.forsIndex[j]?).getD 0))) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings "node")
      =
        (SphincsMinusVerifierSpec.C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
          rw [SphincsMinusVerifierSpec.C13Concrete.forsAllRootsC13_length]
          omega) := by
  rw [SphincsMinusVerifierSpec.C13Concrete.forsAllRootsC13_getElem_normal
    (pk := pk) (digest := digest) (fors := fors) hj]
  exact forsLeafInnerStep_node_eq_forsClimb_of_eval
    st (wordOfHash16 pk.pkSeed) j ((digest.forsIndex[j]?).getD 0)
    ((fors.sk[j]?).getD ⟨#[]⟩) ((fors.authPath[j]?).getD []) cdAt
    hstep hD hm0 hAdrLt hSkLt hTree hSecret hLeaf

/-- One FORS Merkle step preserves the seed slot when its setup bindings and
frozen calldata frame match the C13 FORS auth-path layout. -/
theorem stepMerkle_preserves_seed_slot_of_fors_frozen_calldata
    (s : RuntimeState) (t idx base : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsel : s.selector = 0)
    (hcd : s.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : lookupValue s.bindings "authPtr"
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t))
    (hbase : lookupValue s.bindings "forsBase" = base)
    (hbaselt : base < 2 ^ 256)
    (hpathlt : lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (ht : t < 6)
    (hidx : idx < 19) :
    ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val := by
  rcases s4_eval_site_of_fors_frozen_calldata
      s t idx base pkSeed pkRoot message sig hsel hcd hap hbase hbaselt hpathlt ht hidx with
    ⟨vsib, vadr, hpath, h1, h3⟩
  exact stepMerkle_preserves_seed_slot_of_s4_eval
    s idx (lookupValue s.bindings "pathIdx") vsib vadr rfl hpath h1 h3

/-- One FORS Merkle step preserves an ordinary root-array slot when its setup
bindings and frozen calldata frame match the C13 FORS auth-path layout. -/
theorem stepMerkle_preserves_root_cell_of_fors_frozen_calldata
    (s : RuntimeState) (j t idx base : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsel : s.selector = 0)
    (hcd : s.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : lookupValue s.bindings "authPtr"
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t))
    (hbase : lookupValue s.bindings "forsBase" = base)
    (hbaselt : base < 2 ^ 256)
    (hpathlt : lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (ht : t < 6)
    (hidx : idx < 19) :
    ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
        (0x80 + 32 * j)).val
      = (s.world.memory (0x80 + 32 * j)).val := by
  rcases s4_eval_site_of_fors_frozen_calldata
      s t idx base pkSeed pkRoot message sig hsel hcd hap hbase hbaselt hpathlt ht hidx with
    ⟨vsib, vadr, hpath, h1, h3⟩
  exact stepMerkle_preserves_root_cell_of_s4_eval
    s j idx (lookupValue s.bindings "pathIdx") vsib vadr rfl hpath h1 h3

/-- One inner FORS Merkle step preserves the frozen-site invariant.  The moving
`pathIdx` is rebound to `pathIdx >>> 1`, hence remains a bounded EVM word; the
static selector/calldata and fixed `authPtr`/`treeAdrsBase` bindings are framed
through the step. -/
theorem stepMerkle_preserves_forsFrozenSite
    (s : RuntimeState) (t idx : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ForsFrozenSite t pkSeed pkRoot message sig s)
    (ht : t < 6)
    (hidx : idx < 19) :
    ForsFrozenSite t pkSeed pkRoot message sig
      (stepMerkle "node" "pathIdx" "forsBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }) := by
  rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
  rcases s4_eval_site_of_fors_frozen_calldata
      s t idx base pkSeed pkRoot message sig
      hsel hcd hap hbase hbaselt hpathlt ht hidx with
    ⟨vsib, vadr, _, h1, h3⟩
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let mIdx : Nat := lookupValue s.bindings "pathIdx"
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory :=
        SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "node"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory :=
        SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hpathH : lookupValue stH.bindings "pathIdx" = mIdx := by
    dsimp [stH, mIdx]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "pathIdx" (wordNormalize idx) (by decide)]
  have hpath1 : lookupValue st1.bindings "pathIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "pathIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "pathIdx" st1 mIdx hpath1 hpathlt
  have hpath3 : lookupValue st3.bindings "pathIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "pathIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "pathIdx" st3 mIdx hpath3 hpathlt
  have hsvalt : sval < 2 ^ 256 := by
    dsimp [sval]
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 : lookupValue st4.bindings "s" = sval := by
    dsimp [st4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have h5off : evalExpr [] st4 (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    dsimp [o5]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st4 0x40 sval hs4 (by decide) hsvalt
  have h5val : evalExpr [] st4 (.localVar "node") = some vnode := by
    rfl
  have hs5 : lookupValue st5.bindings "s" = sval := by
    dsimp [st5]
    exact hs4
  have h6off : evalExpr [] st5 (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    dsimp [o6]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st5 0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr [] st5 (.localVar "sibling") =
      some (lookupValue st5.bindings "sibling") := by
    rfl
  have hsc :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_selector_calldata
      "node" "pathIdx" "forsBase" "authPtr" stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      h1 h2 h3 h4 h5off h5val h6off h6val
  have hapStep :
      lookupValue
        (stepMerkle "node" "pathIdx" "forsBase" "authPtr" stH).bindings
          "authPtr"
        = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) := by
    rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_binding_frozen
      "node" "pathIdx" "forsBase" "authPtr" "authPtr" stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h1 h2 h3 h4 h5off h5val h6off h6val]
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "authPtr" (wordNormalize idx) (by decide)]
    exact hap
  have hbaseStep :
      lookupValue
        (stepMerkle "node" "pathIdx" "forsBase" "authPtr" stH).bindings
          "forsBase" = base := by
    rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_binding_frozen
      "node" "pathIdx" "forsBase" "authPtr" "forsBase" stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h1 h2 h3 h4 h5off h5val h6off h6val]
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "forsBase" (wordNormalize idx) (by decide)]
    exact hbase
  have hpathStepEq :
      lookupValue
        (stepMerkle "node" "pathIdx" "forsBase" "authPtr" stH).bindings
          "pathIdx" = vpar :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_idx_binding
      "node" "pathIdx" "forsBase" "authPtr" stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      (by decide) h1 h2 h3 h4 h5off h5val h6off h6val
  have hvparlt : vpar < 2 ^ 256 := by
    dsimp [vpar, mIdx]
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hpathlt
  refine ⟨base, hsc.1.trans hsel, hsc.2.trans hcd, hapStep, hbaseStep, hbaselt, ?_⟩
  rw [hpathStepEq]
  exact hvparlt

/-- Pure inner-loop site invariant: if the C13 FORS frozen-site facts hold at
the loop entry, they hold after every executed `stepMerkle` iteration in a
range whose heights satisfy `idx < 19`.  This is intentionally only a site
invariant; seed/root memory preservation is carried by separate frame lemmas. -/
theorem foldLoop_preserves_forsFrozenSite_range
    (t : Nat) (pkSeed pkRoot message sig : ByteArray) (ht : t < 6) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → i < 19) →
      ForsFrozenSite t pkSeed pkRoot message sig state →
      ForsFrozenSite t pkSeed pkRoot message sig
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
          state index remaining)
  | state, _, 0, _, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
      exact hsite
  | state, index, remaining + 1, hD, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      exact foldLoop_preserves_forsFrozenSite_range t pkSeed pkRoot message sig ht
        (stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { state with bindings := bindValue state.bindings "h" (wordNormalize index) })
        (index + 1) remaining
        (fun i hi1 hi2 => hD i (by omega) (by omega))
        (stepMerkle_preserves_forsFrozenSite
          state t index pkSeed pkRoot message sig hsite ht
          (hD index (by omega) (by omega)))

/-- Pure inner-loop seed-cell frame from the concrete C13 FORS frozen-site
invariant.  This is the cheap fold-level handoff used before lifting back to
statement execution: each first step preserves `mem[0x00]`, while the site
invariant is threaded recursively for the suffix. -/
theorem foldLoop_preserves_seed_slot_of_forsFrozenSite_range
    (t : Nat) (pkSeed pkRoot message sig : ByteArray) (ht : t < 6) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → i < 19) →
      ForsFrozenSite t pkSeed pkRoot message sig state →
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
          state index remaining).world.memory 0).val
        = (state.world.memory 0).val
  | state, _, 0, _, _ => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
  | state, index, remaining + 1, hD, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      let stepState : RuntimeState :=
        stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { state with bindings := bindValue state.bindings "h" (wordNormalize index) }
      have hstepMem : (stepState.world.memory 0).val = (state.world.memory 0).val := by
        rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
        exact stepMerkle_preserves_seed_slot_of_fors_frozen_calldata
          state t index base pkSeed pkRoot message sig
          hsel hcd hap hbase hbaselt hpathlt ht
          (hD index (by omega) (by omega))
      have hstepSite :
          ForsFrozenSite t pkSeed pkRoot message sig stepState := by
        exact stepMerkle_preserves_forsFrozenSite
          state t index pkSeed pkRoot message sig hsite ht
          (hD index (by omega) (by omega))
      have hrec :
          ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
              (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
              stepState (index + 1) remaining).world.memory 0).val
            = (stepState.world.memory 0).val :=
        foldLoop_preserves_seed_slot_of_forsFrozenSite_range
          t pkSeed pkRoot message sig ht stepState (index + 1) remaining
          (fun i hi1 hi2 => hD i (by omega) (by omega))
          hstepSite
      exact hrec.trans hstepMem

/-- Pure inner-loop ordinary-root-cell frame from the concrete C13 FORS
frozen-site invariant.  Inner Merkle climbing writes scratch/seed/node slots but
does not disturb the root array at `0x80 + 32*j`; this fold-level lemma keeps
that fact threaded together with the frozen-site invariant. -/
theorem foldLoop_preserves_root_cell_of_forsFrozenSite_range
    (j t : Nat) (pkSeed pkRoot message sig : ByteArray) (ht : t < 6) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → i < 19) →
      ForsFrozenSite t pkSeed pkRoot message sig state →
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
          state index remaining).world.memory (0x80 + 32 * j)).val
        = (state.world.memory (0x80 + 32 * j)).val
  | state, _, 0, _, _ => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
  | state, index, remaining + 1, hD, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      let stepState : RuntimeState :=
        stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { state with bindings := bindValue state.bindings "h" (wordNormalize index) }
      have hstepMem :
          (stepState.world.memory (0x80 + 32 * j)).val
            = (state.world.memory (0x80 + 32 * j)).val := by
        rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
        exact stepMerkle_preserves_root_cell_of_fors_frozen_calldata
          state j t index base pkSeed pkRoot message sig
          hsel hcd hap hbase hbaselt hpathlt ht
          (hD index (by omega) (by omega))
      have hstepSite :
          ForsFrozenSite t pkSeed pkRoot message sig stepState := by
        exact stepMerkle_preserves_forsFrozenSite
          state t index pkSeed pkRoot message sig hsite ht
          (hD index (by omega) (by omega))
      have hrec :
          ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
              (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
              stepState (index + 1) remaining).world.memory (0x80 + 32 * j)).val
            = (stepState.world.memory (0x80 + 32 * j)).val :=
        foldLoop_preserves_root_cell_of_forsFrozenSite_range
          j t pkSeed pkRoot message sig ht stepState (index + 1) remaining
          (fun i hi1 hi2 => hD i (by omega) (by omega))
          hstepSite
      exact hrec.trans hstepMem

/-- Exact `forsLeafInnerStep` seed-cell adapter from the C13 FORS frozen-site
invariant.  `forsLeafInnerStep` pre-binds `"h" := 0`; that binding is disjoint
from the frozen site fields, so the pure fold seed frame applies directly. -/
theorem forsLeafInnerStep_preserves_seed_slot_of_forsFrozenSite
    (st : RuntimeState) (t : Nat) (pkSeed pkRoot message sig : ByteArray)
    (ht : t < 6)
    (hsite : ForsFrozenSite t pkSeed pkRoot message sig st) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep st).world.memory 0).val
      = (st.world.memory 0).val := by
  let stH : RuntimeState :=
    { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
  have hsiteH : ForsFrozenSite t pkSeed pkRoot message sig stH := by
    rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
    refine ⟨base, hsel, hcd, ?_, ?_, hbaselt, ?_⟩
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "authPtr" (wordNormalize 0) (by decide)]
      exact hap
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "forsBase" (wordNormalize 0) (by decide)]
      exact hbase
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "pathIdx" (wordNormalize 0) (by decide)]
      exact hpathlt
  have hinner :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
          stH 0 (wordNormalize 19)).world.memory 0).val
        = (stH.world.memory 0).val :=
    foldLoop_preserves_seed_slot_of_forsFrozenSite_range
      t pkSeed pkRoot message sig ht stH 0 (wordNormalize 19)
      (fun i _ hi => by
        have hnorm : wordNormalize 19 = 19 := by
          rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
            Nat.mod_eq_of_lt (by decide)]
        rw [hnorm] at hi
        omega)
      hsiteH
  simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep, stH] using hinner

/-- Exact `forsLeafInnerStep` ordinary-root-cell adapter from the C13 FORS
frozen-site invariant. -/
theorem forsLeafInnerStep_preserves_root_cell_of_forsFrozenSite
    (st : RuntimeState) (j t : Nat) (pkSeed pkRoot message sig : ByteArray)
    (ht : t < 6)
    (hsite : ForsFrozenSite t pkSeed pkRoot message sig st) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep st).world.memory
        (0x80 + 32 * j)).val
      = (st.world.memory (0x80 + 32 * j)).val := by
  let stH : RuntimeState :=
    { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
  have hsiteH : ForsFrozenSite t pkSeed pkRoot message sig stH := by
    rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
    refine ⟨base, hsel, hcd, ?_, ?_, hbaselt, ?_⟩
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "authPtr" (wordNormalize 0) (by decide)]
      exact hap
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "forsBase" (wordNormalize 0) (by decide)]
      exact hbase
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "pathIdx" (wordNormalize 0) (by decide)]
      exact hpathlt
  have hinner :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
          (stepMerkle "node" "pathIdx" "forsBase" "authPtr")
          stH 0 (wordNormalize 19)).world.memory (0x80 + 32 * j)).val
        = (stH.world.memory (0x80 + 32 * j)).val :=
    foldLoop_preserves_root_cell_of_forsFrozenSite_range
      j t pkSeed pkRoot message sig ht stH 0 (wordNormalize 19)
      (fun i _ hi => by
        have hnorm : wordNormalize 19 = 19 := by
          rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
            Nat.mod_eq_of_lt (by decide)]
        rw [hnorm] at hi
        omega)
      hsiteH
  simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep, stH] using hinner

/-- One concrete FORS leaf iteration preserves `mem[0x00]` from the actual local
setup facts.  This removes the older arbitrary-state `hsite` premise for a
single leaf: setup packages `ForsFrozenSite`, the inner pure step preserves the
seed slot, and the final store is non-aliasing for `t < 6`. -/
theorem forsLeafStep_preserves_seed_slot_of_forsFrozenSetup
    (st : RuntimeState) (t : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hi : lookupValue st.bindings "i" = t)
    (ht : t < 6)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory 0).val
      = (st.world.memory 0).val := by
  have hbody :
      execStmtList [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody
        = .continue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) :=
    SphincsMinusVerifiers.SegmentS4Fors.execForsLeaf st
  rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody_eq_segments,
    SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue
      st (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupBody
      [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt,
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt]
      (SphincsMinusVerifiers.SegmentS4Fors.execForsLeafSetup st)] at hbody
  have hInnerExec :
      execStmt [] (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
          SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt =
        .continue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)) :=
    SphincsMinusVerifiers.SegmentS4Fors.execForsLeafInner
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
  rw [execStmtList_cons_continue _ _ _
      [SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt] hInnerExec] at hbody
  have hStoreExec :
      execStmt []
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
          SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt =
        .continue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) := by
    simpa using hbody
  have hiSetup :
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
          "i" = t := by
    rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_i st, hi]
  have hiInner :
      lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings
          "i" = t := by
    rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInner_preserves_i
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)) hInnerExec,
      hiSetup]
  have hStoreSeed :=
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStore_preserves_seed_slot_range
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) t ht hiInner hStoreExec
  have hsetupSite :
      ForsFrozenSite t pkSeed pkRoot message sig
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st) :=
    forsLeafSetupStep_forsFrozenSite st t pkSeed pkRoot message sig
      hi ht hsigBase hsel hcd
  have hInnerSeed :=
    forsLeafInnerStep_preserves_seed_slot_of_forsFrozenSite
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      t pkSeed pkRoot message sig ht hsetupSite
  have hSetupSeed :=
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_seed_slot st
  rw [hStoreSeed, hInnerSeed, hSetupSeed]

/-- One concrete FORS leaf iteration preserves an ordinary root slot different
from the leaf being stored, using the actual local setup facts rather than an
arbitrary-state site premise. -/
theorem forsLeafStep_preserves_root_cell_ne_of_forsFrozenSetup
    (st : RuntimeState) (j t : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hi : lookupValue st.bindings "i" = t)
    (ht : t < 6)
    (hne : j ≠ t)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory
        (0x80 + 32 * j)).val
      = (st.world.memory (0x80 + 32 * j)).val := by
  have hbody :
      execStmtList [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody
        = .continue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) :=
    SphincsMinusVerifiers.SegmentS4Fors.execForsLeaf st
  rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody_eq_segments,
    SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue
      st (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupBody
      [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt,
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt]
      (SphincsMinusVerifiers.SegmentS4Fors.execForsLeafSetup st)] at hbody
  have hInnerExec :
      execStmt [] (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
          SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt =
        .continue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)) :=
    SphincsMinusVerifiers.SegmentS4Fors.execForsLeafInner
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
  rw [execStmtList_cons_continue _ _ _
      [SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt] hInnerExec] at hbody
  have hStoreExec :
      execStmt []
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
          SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt =
        .continue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) := by
    simpa using hbody
  have hiSetup :
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
          "i" = t := by
    rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_i st, hi]
  have hiInner :
      lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings
          "i" = t := by
    rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInner_preserves_i
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)) hInnerExec,
      hiSetup]
  have hStoreRoot :=
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStore_preserves_root_cell_range_ne
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) j t ht hiInner hne hStoreExec
  have hsetupSite :
      ForsFrozenSite t pkSeed pkRoot message sig
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st) :=
    forsLeafSetupStep_forsFrozenSite st t pkSeed pkRoot message sig
      hi ht hsigBase hsel hcd
  have hInnerRoot :=
    forsLeafInnerStep_preserves_root_cell_of_forsFrozenSite
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      j t pkSeed pkRoot message sig ht hsetupSite
  have hSetupRoot :=
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_root_cell_range st j
  rw [hStoreRoot, hInnerRoot, hSetupRoot]

/-- One FORS leaf iteration preserves every other ordinary root slot over the
real outer range when each inner Merkle step carries the frozen C13
calldata/auth-path frame. -/
theorem forsLeafStep_preserves_root_cell_range_ne_of_fors_frozen_calldata
    (st : RuntimeState) (j t : Nat) (ht : t < 6)
    (hi : lookupValue st.bindings "i" = t) (hne : j ≠ t)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (idx : Nat), idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
        lookupValue s.bindings "authPtr"
          = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory
        (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val := by
  exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_root_cell_range_ne_of_inner
    st j t ht hi hne
    (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_root_cell_range st j)
    (forsLeafInner_preserves_memory_val_range_of_step
      (0x80 + 32 * j) (fun idx => idx < 19)
      (fun s idx hidx => by
        rcases hsite s idx hidx with
          ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
        exact stepMerkle_preserves_root_cell_of_fors_frozen_calldata
          s j t idx base pkSeed pkRoot message sig
          hsel hcd hap hbase hbaselt hpathlt ht hidx)
      (fun i _ hi => by
        have hnorm : wordNormalize 19 = 19 := by
          rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
            Nat.mod_eq_of_lt (by decide)]
        rw [hnorm] at hi
        omega))

/-- Outer FORS carry for an ordinary root cell with the suffix-preservation
premise discharged from frozen C13 calldata/auth-path facts.  The conclusion is
still local to the model state: callers must separately identify the
iteration-local post-inner `"node"` with the corresponding spec root word. -/
theorem forsOuter_root_cell_eq_iteration_node_of_fors_frozen_calldata
    (st : RuntimeState) (j : Nat) (hj : j < 6)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
        lookupValue s.bindings "authPtr"
          = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
        0 (wordNormalize 6)).world.memory (0x80 + 32 * j)).val =
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              { (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                  { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                      { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") := by
  exact SphincsMinusVerifiers.SegmentS4Fors.forsOuter_root_cell_eq_iteration_node_of_suffix_preserves
    st j hj
    (fun s t hgt ht => by
      have hi : lookupValue (bindValue s.bindings "i" (wordNormalize t)) "i" = t := by
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (lt_trans ht (by decide))]
      exact forsLeafStep_preserves_root_cell_range_ne_of_fors_frozen_calldata
        { s with bindings := bindValue s.bindings "i" (wordNormalize t) }
        j t ht hi (by omega) pkSeed pkRoot message sig
        (fun s idx hidx => hsite s t idx ht hidx))

/-- S4-shaped range-gated adapter for the FORS inner Merkle climb.  The per-step
seed-frame premise may depend on a predicate over the actual inner height. -/
theorem forsLeafInner_preserves_seed_slot_range_of_step
    (D : Nat → Prop)
    (hstep : ∀ (s : RuntimeState) (idx : Nat), D idx →
      ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 19 → D i)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_range
      "node" "pathIdx" "forsBase" "authPtr" 0 19 D hstep st s' hD
      (by simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt] using h)

/-- One FORS leaf iteration preserves `mem[0x00]` over the real outer range once
the inner Merkle step has a bounded-index seed-frame proof. -/
theorem forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hstep : ∀ (s : RuntimeState) (hidx : Nat),
      ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory 0).val
      = (st.world.memory 0).val :=
  SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_seed_slot_range_of_inner
    st idx hidx hi
    (forsLeafInner_preserves_seed_slot_bound_of_step hstep)

/-- Range-gated version of
`forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound`. -/
theorem forsLeafStep_preserves_seed_slot_range_of_merkle_step_range
    (D : Nat → Prop)
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hstep : ∀ (s : RuntimeState) (hidx : Nat), D hidx →
      ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 19 → D i) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory 0).val
      = (st.world.memory 0).val :=
  SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_seed_slot_range_of_inner
    st idx hidx hi
    (forsLeafInner_preserves_seed_slot_range_of_step D hstep hD)

/-- Full FORS outer-loop seed-cell frame reduced to a bounded-index
per-`stepMerkle` seed-frame proof for the inner Merkle climb. -/
theorem execForsOuter_preserves_seed_slot_range_of_merkle_step_bound
    (st s' : RuntimeState)
    (hstep : ∀ (s : RuntimeState) (hidx : Nat),
      ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsOuterStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val :=
  SphincsMinusVerifiers.SegmentS4Fors.execForsOuter_preserves_seed_slot_range_six
    st s'
    (fun s idx hidx s'' hexec => by
      have hi : lookupValue (bindValue s.bindings "i" (wordNormalize idx)) "i" = idx := by
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (lt_trans hidx (by decide))]
      exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody_preserves_seed_slot_range_of_inner
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
          s'' idx hidx hi
          (forsLeafInner_preserves_seed_slot_bound_of_step hstep)
          hexec)
    h

/-- Range-gated version of
`execForsOuter_preserves_seed_slot_range_of_merkle_step_bound`. -/
theorem execForsOuter_preserves_seed_slot_range_of_merkle_step_range
    (D : Nat → Prop)
    (st s' : RuntimeState)
    (hstep : ∀ (s : RuntimeState) (hidx : Nat), D hidx →
      ((stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 19 → D i)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsOuterStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val :=
  SphincsMinusVerifiers.SegmentS4Fors.execForsOuter_preserves_seed_slot_range_six
    st s'
    (fun s idx hidx s'' hexec => by
      have hi : lookupValue (bindValue s.bindings "i" (wordNormalize idx)) "i" = idx := by
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (lt_trans hidx (by decide))]
      exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody_preserves_seed_slot_range_of_inner
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
          s'' idx hidx hi
          (forsLeafInner_preserves_seed_slot_range_of_step D hstep hD)
          hexec)
    h

/-- Full FORS outer-loop seed-cell frame reduced to the S4-shaped per-step eval
site facts: path-index boundedness, masked sibling calldata read, and address
assembly eval at each inner Merkle height. -/
theorem execForsOuter_preserves_seed_slot_range_of_s4_eval
    (st s' : RuntimeState)
    (hsite : ∀ (s : RuntimeState) (idx : Nat),
      ∃ vsib vadr,
        lookupValue s.bindings "pathIdx" < 2 ^ 256 ∧
        evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib ∧
        evalExpr []
            { s with bindings :=
              (bindValue
                (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
                "parentIdx" (lookupValue s.bindings "pathIdx" >>> 1)) }
            (.bitOr (.localVar "forsBase")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsOuterStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val :=
  execForsOuter_preserves_seed_slot_range_of_merkle_step_bound st s'
    (fun s idx => by
      rcases hsite s idx with ⟨vsib, vadr, hlt, h1, h3⟩
      exact stepMerkle_preserves_seed_slot_of_s4_eval
        s idx (lookupValue s.bindings "pathIdx") vsib vadr rfl hlt h1 h3)
    h

/-- One FORS leaf iteration preserves `mem[0x00]` over the real outer range once
each inner Merkle step carries the frozen C13 calldata/auth-path frame.  The
remaining premises are precisely the setup facts for the threaded inner states:
selector/calldata stability, `authPtr`, `treeAdrsBase`, and bounded `pathIdx`. -/
theorem forsLeafStep_preserves_seed_slot_range_of_fors_frozen_calldata
    (st : RuntimeState) (t : Nat) (ht : t < 6)
    (hi : lookupValue st.bindings "i" = t)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (idx : Nat), idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
        lookupValue s.bindings "authPtr"
          = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory 0).val
      = (st.world.memory 0).val :=
  forsLeafStep_preserves_seed_slot_range_of_merkle_step_range
    (fun idx => idx < 19) st t ht hi
    (fun s idx hidx => by
      rcases hsite s idx hidx with
        ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
      exact stepMerkle_preserves_seed_slot_of_fors_frozen_calldata
        s t idx base pkSeed pkRoot message sig hsel hcd hap hbase hbaselt hpathlt ht hidx)
    (fun i _ hi => by
      have hnorm : wordNormalize 19 = 19 := by
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (by decide)]
      rw [hnorm] at hi
      omega)

/-- Full FORS outer-loop seed-cell frame reduced to frozen C13 calldata/auth-path
facts for the inner Merkle states.  This is the range-gated handoff needed by
the accept-path forced-root bridge: the only remaining work is to supply the
setup facts for the concrete states reached at outer `t < 6` and inner
`idx < 19`. -/
theorem execForsOuter_preserves_seed_slot_range_of_fors_frozen_calldata
    (st s' : RuntimeState) (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
        lookupValue s.bindings "authPtr"
          = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsOuterStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val :=
  SphincsMinusVerifiers.SegmentS4Fors.execForsOuter_preserves_seed_slot_range_six
    st s'
    (fun s t ht s'' hexec => by
      have hi : lookupValue (bindValue s.bindings "i" (wordNormalize t)) "i" = t := by
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (lt_trans ht (by decide))]
      exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody_preserves_seed_slot_range_of_inner
        { s with bindings := bindValue s.bindings "i" (wordNormalize t) }
        s'' t ht hi
        (forsLeafInner_preserves_seed_slot_range_of_step
          (fun idx => idx < 19)
          (fun s idx hidx => by
            rcases hsite s t idx ht hidx with
              ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
            exact stepMerkle_preserves_seed_slot_of_fors_frozen_calldata
              s t idx base pkSeed pkRoot message sig
              hsel hcd hap hbase hbaselt hpathlt ht hidx)
          (fun i _ hi => by
            have hnorm : wordNormalize 19 = 19 := by
              rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
                Nat.mod_eq_of_lt (by decide)]
            rw [hnorm] at hi
            omega))
        hexec)
    h

#print axioms forsLeafInner_preserves_seed_slot_bound_of_step
#print axioms forsLeafInner_preserves_memory_val_bound_of_step
#print axioms forsLeafInner_preserves_memory_val_range_of_step
#print axioms forsLeafStep_preserves_root_cell_range_ne_of_inner_step
#print axioms forsLeafStep_preserves_root_cell_range_ne_of_s4_eval
#print axioms forsOuter_root_cell_eq_iteration_node_of_s4_eval
#print axioms forsLeafStep_preserves_root_cell_range_ne_of_fors_frozen_calldata
#print axioms forsOuter_root_cell_eq_iteration_node_of_fors_frozen_calldata
#print axioms forsLeafInner_preserves_seed_slot_range_of_step
#print axioms stepMerkle_forsFrame_hstep_of_s4_data
#print axioms stepMerkle_forsFrame_hstep_of_fors_frozen_calldata
#print axioms stepMerkle_preserves_seed_slot_of_s4_eval
#print axioms stepMerkle_preserves_root_cell_of_s4_eval
#print axioms forsLeafInner_preserves_seed_slot_bound_of_s4_eval
#print axioms s4_address_assembly_eval_exists
#print axioms s4_eval_site_of_frozen_calldata
#print axioms s4_eval_site_of_fors_frozen_calldata
#print axioms forsLeafSetupStep_fors_frozen_calldata_site
#print axioms forsLeafSetupStep_forsFrozenSite
#print axioms forsLeafSetupStep_initial_forsClimbRel_of_eval
#print axioms forsLeafSetupStep_initial_forsClimbFrame_of_eval_site
#print axioms forsLeafInnerStep_node_eq_forsClimb_of_eval
#print axioms forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site
#print axioms forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site_range
#print axioms forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site_range_path_bound
#print axioms forsLeafInnerStep_node_eq_forsClimbFrame_of_fors_frozen_calldata
#print axioms forsLeafInnerStep_node_eq_forsAllRootsC13_getElem_of_eval
#print axioms stepMerkle_preserves_seed_slot_of_fors_frozen_calldata
#print axioms stepMerkle_preserves_root_cell_of_fors_frozen_calldata
#print axioms stepMerkle_preserves_forsFrozenSite
#print axioms foldLoop_preserves_forsFrozenSite_range
#print axioms foldLoop_preserves_seed_slot_of_forsFrozenSite_range
#print axioms foldLoop_preserves_root_cell_of_forsFrozenSite_range
#print axioms forsLeafInnerStep_preserves_seed_slot_of_forsFrozenSite
#print axioms forsLeafInnerStep_preserves_root_cell_of_forsFrozenSite
#print axioms forsLeafStep_preserves_seed_slot_of_forsFrozenSetup
#print axioms forsLeafStep_preserves_root_cell_ne_of_forsFrozenSetup
#print axioms forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound
#print axioms forsLeafStep_preserves_seed_slot_range_of_merkle_step_range
#print axioms execForsOuter_preserves_seed_slot_range_of_merkle_step_bound
#print axioms execForsOuter_preserves_seed_slot_range_of_merkle_step_range
#print axioms execForsOuter_preserves_seed_slot_range_of_s4_eval
#print axioms forsLeafStep_preserves_seed_slot_range_of_fors_frozen_calldata
#print axioms execForsOuter_preserves_seed_slot_range_of_fors_frozen_calldata

end SphincsMinusVerifiers.SegmentS4ForsMerkleFrame
