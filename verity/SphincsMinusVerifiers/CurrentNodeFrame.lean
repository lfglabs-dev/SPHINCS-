/-
  CurrentNodeFrame — structural adapters for the left operand of C13's final
  `currentNode == root` comparison.

  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_root` reduces the
  remaining accept-path data obligation to:

      lookupValue (afterLayer (mkC13State ...)).bindings "currentNode"
        = wordOfHash16 specRoot

  This file packages the pure loop-composition part of that obligation.  It does
  not prove the per-layer WOTS/XMSS keccak correspondence; instead it shows that
  once a one-layer correspondence is available, the existing `afterLayer` fold
  carries it from the `afterSeed` start state to the final comparison operand.

  No `execC13`, no bridge axiom, no `sorry`, no `native_decide`.
-/

import SphincsMinusVerifiers.SegmentCompose
import SphincsMinusVerifiers.MkC13State
import SphincsMinusVerifiers.SegmentS2
import SphincsMinusVerifiers.SegmentS4Finalize
import SphincsMinusVerifiers.SegmentSeed
import SphincsMinusVerifiers.SegmentLayer3
import SphincsMinusVerifiers.KeccakBridge
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.CurrentNodeFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.ClimbKit (N_MASK)
open SphincsMinusVerifierSpec
open SphincsMinusVerifierSpec.C13Concrete (adrsForsRoots keccakWords maskN nMask wordOfHash16)

/-! ## Seed boundary. -/

/-- The S2 H_msg block writes the public seed word to scratch slot `0x00` in the
frozen entry state. -/
theorem afterS2_seed_slot_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    ((afterS2 (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed :=
  SegmentS2.s2Step_seed_mkC13State pkSeed pkRoot message sig

/-- S3 only updates bindings, so it preserves the seed scratch cell written by
S2. -/
theorem afterS3_seed_slot_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    ((afterS3 (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  unfold afterS3 SegmentS3.stepS3
  exact afterS2_seed_slot_mkC13State pkSeed pkRoot message sig

/-- Loop-plumbing adapter for the FORS outer loop: once the per-iteration
`forsLeafStep` memory-frame fact is available for a seed cell, the whole
`afterFors` fold preserves that cell back to `afterS3`. -/
theorem afterFors_seed_slot_of_forsLeafStep_preserves
    (st : RuntimeState)
    (hLeaf : ∀ s,
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep s).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors st).world.memory 0).val = ((afterS3 st).world.memory 0).val := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_memory_val "i"
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep 0 hLeaf
    { (afterS3 st) with bindings := bindValue (afterS3 st).bindings "i" (wordNormalize 0) }
    0 (wordNormalize 6)]

/-- Bounded-index version of the FORS seed-cell loop plumbing.  This is the
shape needed by the real outer loop: the final leaf store is known non-aliasing
only after the loop binds `"i"` to its concrete iteration value. -/
theorem afterFors_seed_slot_of_forsLeafStep_bound_preserves
    (st : RuntimeState)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat),
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors st).world.memory 0).val = ((afterS3 st).world.memory 0).val := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_memory_val_bound "i"
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep 0 hLeaf
    { (afterS3 st) with bindings := bindValue (afterS3 st).bindings "i" (wordNormalize 0) }
    0 (wordNormalize 6)]

/-- Range-gated FORS seed-cell loop plumbing.  The real statement-14 loop runs
six iterations, so callers only need a leaf-step memory frame for `idx < 6`. -/
theorem afterFors_seed_slot_of_forsLeafStep_range_preserves
    (st : RuntimeState)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors st).world.memory 0).val = ((afterS3 st).world.memory 0).val := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "i"
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep 0 (fun idx => idx < 6)
    (fun s idx hidx => hLeaf s idx hidx)
    { (afterS3 st) with bindings := bindValue (afterS3 st).bindings "i" (wordNormalize 0) }
    0 (wordNormalize 6)
    (fun i _ hi => by
      have hbound : i < 6 := by
        simpa using hi
      exact hbound)]

/-- Frozen-entry version of `afterFors_seed_slot_of_forsLeafStep_preserves`,
composed with the S2/S3 seed endpoint. -/
theorem afterFors_seed_slot_mkC13State_of_forsLeafStep_preserves
    (pkSeed pkRoot message sig : ByteArray)
    (hLeaf : ∀ s,
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep s).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  rw [afterFors_seed_slot_of_forsLeafStep_preserves _ hLeaf]
  exact afterS3_seed_slot_mkC13State pkSeed pkRoot message sig

/-- Frozen-entry bounded-index version of
`afterFors_seed_slot_of_forsLeafStep_bound_preserves`. -/
theorem afterFors_seed_slot_mkC13State_of_forsLeafStep_bound_preserves
    (pkSeed pkRoot message sig : ByteArray)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat),
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  rw [afterFors_seed_slot_of_forsLeafStep_bound_preserves _ hLeaf]
  exact afterS3_seed_slot_mkC13State pkSeed pkRoot message sig

/-- Frozen-entry range-gated version of
`afterFors_seed_slot_of_forsLeafStep_range_preserves`. -/
theorem afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves
    (pkSeed pkRoot message sig : ByteArray)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  rw [afterFors_seed_slot_of_forsLeafStep_range_preserves _ hLeaf]
  exact afterS3_seed_slot_mkC13State pkSeed pkRoot message sig

/-- `afterSeed` starts the hypertree climb at the FORS public-key word. -/
theorem afterSeed_currentNode (st : RuntimeState) :
    lookupValue (afterSeed st).bindings "currentNode"
      = lookupValue (afterFinalize st).bindings "forsPk" := by
  unfold afterSeed
  exact SegmentSeed.stepSeed_currentNode (afterFinalize st)

/-- `afterSeed` starts the hypertree index from the digest-derived `htIdx`. -/
theorem afterSeed_idxTree (st : RuntimeState) :
    lookupValue (afterSeed st).bindings "idxTree"
      = lookupValue (afterFinalize st).bindings "htIdx" := by
  unfold afterSeed
  exact SegmentSeed.stepSeed_idxTree (afterFinalize st)

/-- `afterSeed` starts the layer signature offset at the first XMSS layer. -/
theorem afterSeed_sigOff (st : RuntimeState) :
    lookupValue (afterSeed st).bindings "sigOff" = wordNormalize 1952 := by
  unfold afterSeed
  exact SegmentSeed.stepSeed_sigOff (afterFinalize st)

/-! ## FORS-finalize boundary. -/

/-- The model word produced by statement 21's FORS-root compression keccak, exposed
at the `afterFors`/`afterFinalize` boundary. -/
def forsPkCompressWord (st : RuntimeState) : Nat :=
  (Verity.Core.Uint256.and
    (keccakMemorySlice
      (SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory
      (wordNormalize 0x00) (wordNormalize 0x120))
    (wordNormalize N_MASK)).val

/-- If the S4 memory-compression word equals the spec FORS public key word, then
`afterFinalize` binds `"forsPk"` to that spec word.  This isolates the remaining
S4 data-correspondence obligation from the seed/layer composition. -/
theorem afterFinalize_forsPk_of_compress
    (st : RuntimeState) (forsPk : ByteArray)
    (hCompress : forsPkCompressWord (afterFors st) = wordOfHash16 forsPk) :
    lookupValue (afterFinalize st).bindings "forsPk" = wordOfHash16 forsPk := by
  unfold afterFinalize
  rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeStep_forsPk]
  exact hCompress

/-- If the pre-`forsPk` scratch frame contains
`seed ‖ FORS_ROOTS adrs ‖ root_0..root_6`, then the model's FORS public-key
compression word is exactly the spec kernel's masked compression word.  This is
the final keccak/masking half of the S4 obligation; the caller still has to prove
that the seven scratch roots are the roots produced by the FORS climbs. -/
theorem forsPkCompressWord_eq_of_memory
    (st : RuntimeState) (seed : Nat) (roots : List Nat)
    (hlen : roots.length = 7)
    (hm0 :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory 0).val
        = seed)
    (hm1 :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory 0x20).val
        = adrsForsRoots)
    (hmR : ∀ j, (h : j < 7) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory
          (0x40 + 32 * j)).val = roots[j]'(by omega)) :
    forsPkCompressWord st = maskN (keccakWords (seed :: adrsForsRoots :: roots)) := by
  unfold forsPkCompressWord
  rw [show wordNormalize 0x00 = 0 by rfl]
  rw [show wordNormalize 0x120 = 0x120 by rfl]
  rw [show (N_MASK : Nat) = nMask from rfl]
  have hnmask : wordNormalize nMask = nMask := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt (by decide)
  rw [hnmask]
  have hlen9 : (seed :: adrsForsRoots :: roots).length = 9 := by
    simp [hlen]
  have hsz : 32 * (seed :: adrsForsRoots :: roots).length = 0x120 := by
    rw [hlen9]
  rw [← hsz]
  rw [KeccakBridge.keccakMemorySlice_eq_keccakWords]
  · unfold maskN Verity.Core.Uint256.and Verity.Core.Uint256.ofNat
    simp only
    have hklt : keccakWords (seed :: adrsForsRoots :: roots) < Verity.Core.Uint256.modulus := by
      simpa [Compiler.Constants.evmModulus] using
        KeccakBridge.keccakWords_lt (seed :: adrsForsRoots :: roots)
    have hnlt : nMask < Verity.Core.Uint256.modulus := by
      decide
    rw [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hnlt]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hklt)
  · intro i hi
    rw [hlen9] at hi
    match i with
    | 0 => simpa using hm0
    | 1 => simpa using hm1
    | j + 2 =>
      have hj : j < 7 := by omega
      have hoff : 0 + 32 * (j + 2) = 0x40 + 32 * j := by omega
      rw [hoff]
      exact hmR j hj

/-- Variant of `forsPkCompressWord_eq_of_memory` that consumes the seven FORS
root words from the state before the copy loop.  `SegmentS4Finalize` proves the
copy loop moves those words into the compression preimage slots without changing
their values. -/
theorem forsPkCompressWord_eq_of_preCopy_roots
    (st : RuntimeState) (seed : Nat) (roots : List Nat)
    (hlen : roots.length = 7)
    (hm0 :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory 0).val
        = seed)
    (hm1 :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory 0x20).val
        = adrsForsRoots)
    (hmR : ∀ j, (h : j < 7) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep st).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega)) :
    forsPkCompressWord st = maskN (keccakWords (seed :: adrsForsRoots :: roots)) :=
  forsPkCompressWord_eq_of_memory st seed roots hlen hm0 hm1
    (fun j hj => by
      rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep_copy_slot st j hj]
      exact hmR j hj)

/-- Full S4-finalize compression adapter phrased at the most useful boundary:
the seed cell is read from the incoming state, the FORS_ROOTS ADRS cell is
discharged by `SegmentS4Finalize`, the roots are read from the state immediately
before the copy loop, and the copy loop itself is discharged by
`SegmentS4Finalize`.  The remaining S4 data facts are thus the seed value and the
actual root contents of the pre-copy cells. -/
theorem forsPkCompressWord_eq_of_preCopy_frame
    (st : RuntimeState) (seed : Nat) (roots : List Nat)
    (hlen : roots.length = 7)
    (hmSeed : (st.world.memory 0).val = seed)
    (hmR : ∀ j, (h : j < 7) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep st).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega)) :
    forsPkCompressWord st = maskN (keccakWords (seed :: adrsForsRoots :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_roots st seed roots hlen
    (by
      rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep_preserves_low_slot st 0
        (by decide)]
      rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_seed_slot st]
      exact hmSeed)
    (by
      rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep_preserves_low_slot st 0x20
        (by decide)]
      exact SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_adrsRoots_slot st)
    hmR

/-- Variant of `forsPkCompressWord_eq_of_preCopy_frame` matching the concrete S4
layout just before the copy loop: the first six FORS roots live in
`0x80 + 32*j`, while the seventh forced-zero tree root lives at `0x140`
(`0x80 + 32*6`).  The FORS_ROOTS address word is proved by the finalize segment,
so callers only supply seed and root-cell facts. -/
theorem forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
    (st : RuntimeState) (seed : Nat) (roots : List Nat)
    (hlen : roots.length = 7)
    (hmSeed : (st.world.memory 0).val = seed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep st).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep st).world.memory
          0x140).val = roots[6]'(by omega)) :
    forsPkCompressWord st = maskN (keccakWords (seed :: adrsForsRoots :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_frame st seed roots hlen hmSeed
    (fun j hj => by
      by_cases hj6 : j < 6
      · exact hmRlo j hj6
      · have hjeq : j = 6 := by omega
        simpa [hjeq] using hmRlast)

/-- Frozen-entry FORS-compression adapter: the seed word is supplied by the
S2/S3 seed-cell endpoint plus the outer-FORS loop memory-frame hypothesis, while
the root-cell facts remain the substantive FORS climb correspondence obligations. -/
theorem forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last
    (pkSeed pkRoot message sig : ByteArray) (roots : List Nat)
    (hlen : roots.length = 7)
    (hLeaf : ∀ s,
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep s).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega)) :
    forsPkCompressWord (afterFors (mkC13State pkSeed pkRoot message sig))
      = maskN (keccakWords (wordOfHash16 pkSeed :: adrsForsRoots :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
    (afterFors (mkC13State pkSeed pkRoot message sig)) (wordOfHash16 pkSeed) roots hlen
    (afterFors_seed_slot_mkC13State_of_forsLeafStep_preserves pkSeed pkRoot message sig hLeaf)
    hmRlo hmRlast

/-- Range-gated frozen-entry FORS-compression adapter.  This is the same
boundary as `forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last`, but
the seed preservation premise matches the real statement-14 loop range (`i < 6`)
instead of requiring a globally quantified leaf-step fact. -/
theorem forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last_range
    (pkSeed pkRoot message sig : ByteArray) (roots : List Nat)
    (hlen : roots.length = 7)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega)) :
    forsPkCompressWord (afterFors (mkC13State pkSeed pkRoot message sig))
      = maskN (keccakWords (wordOfHash16 pkSeed :: adrsForsRoots :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
    (afterFors (mkC13State pkSeed pkRoot message sig)) (wordOfHash16 pkSeed) roots hlen
    (afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves
      pkSeed pkRoot message sig hLeaf)
    hmRlo hmRlast

/-- Seed-cell frozen-entry FORS-compression adapter.  This is the narrowest
S4/FORS-compression boundary: callers supply the single seed-cell fact at
`afterFors`, plus the six normal root cells and the forced-root cell. -/
theorem forsPkCompressWord_eq_of_afterFors_seed_mkC13State_six_plus_last
    (pkSeed pkRoot message sig : ByteArray) (roots : List Nat)
    (hlen : roots.length = 7)
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega)) :
    forsPkCompressWord (afterFors (mkC13State pkSeed pkRoot message sig))
      = maskN (keccakWords (wordOfHash16 pkSeed :: adrsForsRoots :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
    (afterFors (mkC13State pkSeed pkRoot message sig)) (wordOfHash16 pkSeed) roots hlen
    hmSeed hmRlo hmRlast

/-! ## Layer-loop lift for `currentNode`. -/

/-- A compact relation saying that a runtime state's `"currentNode"` binding is
the word encoding of a spec-side byte node. -/
def CurrentNodeRel {α : Type} (toWord : α → Nat) (st : RuntimeState) (a : α) : Prop :=
  lookupValue st.bindings "currentNode" = toWord a

/-- One-layer adapter from the structural `stepLayer` fact to the relation used
by the final accept composition.  The caller supplies the real data proof that
the post-layer `"merkleNode"` is the spec step's word image; this lemma handles
the final assignment `currentNode := merkleNode`. -/
theorem stepLayer_currentNodeRel_of_merkleNode
    (s : RuntimeState) (specStep : Nat → Bytes → Bytes) (node : Bytes) (idx : Nat)
    (hMerkle :
      lookupValue
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
          "merkleNode"
        = wordOfHash16 (specStep idx node)) :
    CurrentNodeRel wordOfHash16
      (SegmentLayer3.stepLayer
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
      (specStep idx node) := by
  unfold CurrentNodeRel
  rw [SegmentLayer3.stepLayer_currentNode_eq_merkleNode]
  exact hMerkle

/-- If one `stepLayer` iteration tracks a spec step on the `"currentNode"` word,
then the whole `afterLayer` fold tracks the corresponding `specFold`.

This is the layer-loop shape needed for the eventual `hCurrent` proof.  The
per-layer hypothesis is deliberately abstract: callers can instantiate `α` with a
rich spec accumulator carrying `idxTree`, `sigOff`, parsed layer data, or just the
current byte node, depending on how the WOTS/XMSS correspondence is packaged. -/
theorem afterLayer_currentNode_of_step
    {α : Type} (st : RuntimeState)
    (specStep : Nat → α → α) (toWord : α → Nat) (a0 afinal : α)
    (hStart : lookupValue (afterSeed st).bindings "currentNode" = toWord a0)
    (hStep : ∀ (s : RuntimeState) (a : α) (idx : Nat),
        CurrentNodeRel toWord s a →
        CurrentNodeRel toWord
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx a))
    (hFinal : ClimbLoop.specFold specStep a0 0 (wordNormalize 2) = afinal) :
    lookupValue (afterLayer st).bindings "currentNode" = toWord afinal := by
  let init : RuntimeState :=
    { (afterSeed st) with
      bindings := bindValue (afterSeed st).bindings "layer" (wordNormalize 0) }
  have hStartInit : CurrentNodeRel toWord init a0 := by
    unfold CurrentNodeRel init
    rw [MemoryKit.lookupValue_bindValue_ne
      (afterSeed st).bindings "layer" "currentNode" (wordNormalize 0) (by decide)]
    exact hStart
  have hFold := ClimbLoop.foldLoop_invariant "layer" SegmentLayer3.stepLayer
    specStep (CurrentNodeRel toWord) hStep init a0 0 (wordNormalize 2) hStartInit
  unfold afterLayer
  change CurrentNodeRel toWord
      (ClimbLoop.foldLoop "layer" SegmentLayer3.stepLayer init 0 (wordNormalize 2)) afinal
  rw [← hFinal]
  exact hFold

/-- Same loop adapter, with the start fact supplied at the FORS-finalize boundary:
if `afterFinalize.forsPk` is the word image of the initial spec accumulator, and
each layer step preserves the relation, then the final compare's left operand is
the word image of the folded spec accumulator. -/
theorem afterLayer_currentNode_of_forsPk_step
    {α : Type} (st : RuntimeState)
    (specStep : Nat → α → α) (toWord : α → Nat) (a0 afinal : α)
    (hForsPk : lookupValue (afterFinalize st).bindings "forsPk" = toWord a0)
    (hStep : ∀ (s : RuntimeState) (a : α) (idx : Nat),
        CurrentNodeRel toWord s a →
        CurrentNodeRel toWord
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx a))
    (hFinal : ClimbLoop.specFold specStep a0 0 (wordNormalize 2) = afinal) :
    lookupValue (afterLayer st).bindings "currentNode" = toWord afinal :=
  afterLayer_currentNode_of_step st specStep toWord a0 afinal
    (by rw [afterSeed_currentNode, hForsPk]) hStep hFinal

/-- Byte-node specialization of `afterLayer_currentNode_of_forsPk_step`, phrased
exactly in the `wordOfHash16` form expected by `SegmentAcceptSpec`. -/
theorem afterLayer_currentNode_wordOfHash16_of_forsPk_step
    (st : RuntimeState)
    (specStep : Nat → Bytes → Bytes) (startNode finalNode : Bytes)
    (hForsPk : lookupValue (afterFinalize st).bindings "forsPk" = wordOfHash16 startNode)
    (hStep : ∀ (s : RuntimeState) (node : Bytes) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hFinal : ClimbLoop.specFold specStep startNode 0 (wordNormalize 2) = finalNode) :
    lookupValue (afterLayer st).bindings "currentNode" = wordOfHash16 finalNode :=
  afterLayer_currentNode_of_forsPk_step st specStep wordOfHash16 startNode finalNode
    hForsPk hStep hFinal

/-! ## Axiom audit. -/

#print axioms afterSeed_currentNode
#print axioms afterS2_seed_slot_mkC13State
#print axioms afterS3_seed_slot_mkC13State
#print axioms afterFors_seed_slot_of_forsLeafStep_preserves
#print axioms afterFors_seed_slot_of_forsLeafStep_bound_preserves
#print axioms afterFors_seed_slot_of_forsLeafStep_range_preserves
#print axioms afterFors_seed_slot_mkC13State_of_forsLeafStep_preserves
#print axioms afterFors_seed_slot_mkC13State_of_forsLeafStep_bound_preserves
#print axioms afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves
#print axioms afterSeed_idxTree
#print axioms afterSeed_sigOff
#print axioms afterFinalize_forsPk_of_compress
#print axioms forsPkCompressWord_eq_of_memory
#print axioms forsPkCompressWord_eq_of_preCopy_roots
#print axioms forsPkCompressWord_eq_of_preCopy_frame
#print axioms forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
#print axioms forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last
#print axioms forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last_range
#print axioms forsPkCompressWord_eq_of_afterFors_seed_mkC13State_six_plus_last
#print axioms stepLayer_currentNodeRel_of_merkleNode
#print axioms afterLayer_currentNode_of_step
#print axioms afterLayer_currentNode_of_forsPk_step
#print axioms afterLayer_currentNode_wordOfHash16_of_forsPk_step

end SphincsMinusVerifiers.CurrentNodeFrame
