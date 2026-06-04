/-
  SegmentLayer3MerkleFrame — lightweight adapters for the C13/C12 XMSS layer
  Merkle climb.

  This module mirrors the S4 FORS Merkle-frame adapters, but instantiates the
  generic branchless-Merkle memory frame with the layer-body variable names:
  `"merkleNode"`, `"mIdx"`, `"treeAdrs"`, and `"merklePtr"`.  It intentionally
  sits outside `SegmentLayer3` so the core layer-body reconstruction does not
  import the heavier `ClimbMemFrameMerkle` module.
-/

import SphincsMinusVerifiers.SegmentLayer3
import SphincsMinusVerifiers.ClimbMemFrameMerkle

namespace SphincsMinusVerifiers.SegmentLayer3MerkleFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbKit (stepMerkle)

/-- Layer-shaped local `stepMerkle` seed-cell frame.  For the actual XMSS layer
climb variable names, the pure parent-index, selector, child-offset, and local
load facts are discharged here.  Callers only supply the site-specific masked
sibling calldata read (`h1`) and address assembly eval (`h3`). -/
theorem stepMerkle_preserves_seed_slot_of_layer_eval
    (s : RuntimeState) (idx mIdx vsib vadr : Nat)
    (hmIdx : lookupValue s.bindings "mIdx" = mIdx)
    (hmIdxLt : mIdx < 2 ^ 256)
    (h1 : evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar "merklePtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib)
    (h3 : evalExpr []
            { s with bindings :=
              (bindValue
                (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
                "parentIdx" (mIdx >>> 1)) }
            (.bitOr (.localVar "treeAdrs")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr) :
    ((stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr"
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
  let vnode : Nat := lookupValue st4.bindings "merkleNode"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hmIdxH : lookupValue stH.bindings "mIdx" = mIdx := by
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "mIdx" (wordNormalize idx) (by decide)]
    exact hmIdx
  have hmIdx1 : lookupValue st1.bindings "mIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "mIdx" vsib (by decide)]
    exact hmIdxH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "mIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "mIdx" st1 mIdx hmIdx1 hmIdxLt
  have hmIdx3 : lookupValue st3.bindings "mIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "mIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "mIdx" vsib (by decide)]
    exact hmIdxH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "mIdx" st3 mIdx hmIdx3 hmIdxLt
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
  have h5val : evalExpr [] st4 (.localVar "merkleNode") = some vnode := by
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
  change ((stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" stH).world.memory 0).val
      = (stH.world.memory 0).val
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_mem_zero_val_of_parity
    "merkleNode" "mIdx" "treeAdrs" "merklePtr" stH
    vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
    mIdx hparOff h1 h2 h3 h4 h5off h5val h6off h6val

/-- The remaining C13/C12 layer-site facts needed to prove that one XMSS Merkle
step preserves seed cell `0x00`: bounded `"mIdx"`, the masked auth-sibling load,
and the assembled parent ADRS word. -/
def LayerMerkleEvalFacts (s : RuntimeState) (idx : Nat) : Prop :=
  ∃ mIdx vsib vadr,
    lookupValue s.bindings "mIdx" = mIdx ∧
    mIdx < 2 ^ 256 ∧
    evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "merklePtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      = some vsib ∧
    evalExpr []
        { s with bindings :=
          (bindValue
            (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
            "parentIdx" (mIdx >>> 1)) }
        (.bitOr (.localVar "treeAdrs")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr

/-- One accepting layer iteration preserves seed cell `0x00` once the WOTS/copy
loop frames are supplied and the Merkle loop's per-height site facts are reduced
to `LayerMerkleEvalFacts`. -/
theorem stepLayer_preserves_memory_zero_of_layer_eval_range
    (ls : RuntimeState) (D : Nat → Prop)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (.literal 43) SegmentLayer3.wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (.literal 43) SegmentLayer3.copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hFacts :
      ∀ (s : RuntimeState) (idx : Nat), D idx → LayerMerkleEvalFacts s idx)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 11 → D i) :
    ((SegmentLayer3.stepLayer ls).world.memory 0x00).val =
      ((SegmentLayer3.afterDigit ls).world.memory 0x00).val := by
  refine SegmentLayer3.stepLayer_preserves_memory_zero_of_loop_frames_range
    ls D hWots hCopy ?_ hD
  intro s idx hidx
  rcases hFacts s idx hidx with ⟨mIdx, vsib, vadr, hmIdx, hmIdxLt, h1, h3⟩
  exact stepMerkle_preserves_seed_slot_of_layer_eval
    s idx mIdx vsib vadr hmIdx hmIdxLt h1 h3

#print axioms stepMerkle_preserves_seed_slot_of_layer_eval
#print axioms LayerMerkleEvalFacts
#print axioms stepLayer_preserves_memory_zero_of_layer_eval_range

end SphincsMinusVerifiers.SegmentLayer3MerkleFrame
