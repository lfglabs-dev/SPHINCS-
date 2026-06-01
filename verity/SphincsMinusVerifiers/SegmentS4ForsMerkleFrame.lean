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
            (.bitOr (.localVar "treeAdrsBase")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr) :
    ((stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr"
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
  change ((stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr" stH).world.memory 0).val
      = (stH.world.memory 0).val
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_mem_zero_val_of_parity
    "node" "pathIdx" "treeAdrsBase" "authPtr" stH
    vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
    mIdx hparOff h1 h2 h3 h4 h5off h5val h6off h6val

/-- S4-shaped bounded-index adapter for the FORS inner Merkle climb: if each
`stepMerkle` iteration preserves `mem[0x00]` after the loop binds the concrete
height to `"h"`, then the whole `forsLeafInnerStmt` preserves the seed cell. -/
theorem forsLeafInner_preserves_seed_slot_bound_of_step
    (hstep : ∀ (s : RuntimeState) (idx : Nat),
      ((stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_bound
      "node" "pathIdx" "treeAdrsBase" "authPtr" 0 19 hstep st s'
      (by simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt] using h)

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
            (.bitOr (.localVar "treeAdrsBase")
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
    (hbase : lookupValue s.bindings "treeAdrsBase" = base)
    (hbaselt : base < 2 ^ 256)
    (hpathlt : lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (hidx : idx < 19) :
    ∃ vadr,
      evalExpr []
          { s with bindings :=
            (bindValue
              (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
              "parentIdx" (lookupValue s.bindings "pathIdx" >>> 1)) }
          (.bitOr (.localVar "treeAdrsBase")
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
  have hbase_eval : evalExpr [] stA (.localVar "treeAdrsBase") = some base := by
    show some (lookupValue stA.bindings "treeAdrsBase") = some base
    dsimp [stA]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "treeAdrsBase" (lookupValue s.bindings "pathIdx" >>> 1) (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx))
      "sibling" "treeAdrsBase" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "treeAdrsBase" (wordNormalize idx) (by decide)]
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
    stA (.localVar "treeAdrsBase")
    (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      (.localVar "parentIdx")) base inner hbase_eval hinner hbaselt
    (Nat.bitwise_lt_two_pow hshlt hplt)

/-- S4-shaped range-gated adapter for the FORS inner Merkle climb.  The per-step
seed-frame premise may depend on a predicate over the actual inner height. -/
theorem forsLeafInner_preserves_seed_slot_range_of_step
    (D : Nat → Prop)
    (hstep : ∀ (s : RuntimeState) (idx : Nat), D idx →
      ((stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 19 → D i)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_range
      "node" "pathIdx" "treeAdrsBase" "authPtr" 0 19 D hstep st s' hD
      (by simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt] using h)

/-- One FORS leaf iteration preserves `mem[0x00]` over the real outer range once
the inner Merkle step has a bounded-index seed-frame proof. -/
theorem forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hstep : ∀ (s : RuntimeState) (hidx : Nat),
      ((stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr"
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
      ((stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr"
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
      ((stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr"
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
      ((stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr"
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
            (.bitOr (.localVar "treeAdrsBase")
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

#print axioms forsLeafInner_preserves_seed_slot_bound_of_step
#print axioms forsLeafInner_preserves_seed_slot_range_of_step
#print axioms stepMerkle_preserves_seed_slot_of_s4_eval
#print axioms forsLeafInner_preserves_seed_slot_bound_of_s4_eval
#print axioms s4_address_assembly_eval_exists
#print axioms forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound
#print axioms forsLeafStep_preserves_seed_slot_range_of_merkle_step_range
#print axioms execForsOuter_preserves_seed_slot_range_of_merkle_step_bound
#print axioms execForsOuter_preserves_seed_slot_range_of_merkle_step_range
#print axioms execForsOuter_preserves_seed_slot_range_of_s4_eval

end SphincsMinusVerifiers.SegmentS4ForsMerkleFrame
