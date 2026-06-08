/-
  C13WotsOuterInputs — compact entry-state discharge for the C13 WOTS-outer
  loop inputs.

  The WOTS-PK keccak assembly (`C13WotsPkKeccak`) and the chain-cell closure
  (`C13ChainCells`) both consume five universally-quantified facts about every
  prefix `foldLoop "i" wotsOuterStep st 0 j` (j < 43): the seed cell `0x00`, and
  the bindings `d`, `wotsAdrs`, `wotsPtr`, plus a `calldataload` evaluation.

  The first four are loop *frames*: the WOTS-outer step never rewrites those
  sites, so each prefix value equals the corresponding entry-state value.  This
  module isolates that reasoning as four lightweight lemmas driven by the generic
  `foldLoop_preserves_lookup` / `foldLoop_preserves_memory_val_range` engines, so
  the heavy assembly only needs a compact entry record (`C13WotsOuterEntry`)
  rather than five spelled-out invariants.
-/

import SphincsMinusVerifiers.SegmentLayer3CopyCells

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbLoop (foldLoop)

/-- Frame lemma: any binding `key` distinct from the WOTS-outer body's writes
(`digit`/`steps`/`val`/`chainBase`/`step`) and the loop variable `i` keeps its
entry value through every prefix of the WOTS-outer fold. -/
theorem wotsOuterFold_preserves_binding
    (st : RuntimeState) (key : String)
    (hneDigit : "digit" ≠ key) (hneSteps : "steps" ≠ key)
    (hneVal : "val" ≠ key) (hneChainBase : "chainBase" ≠ key)
    (hneStep : "step" ≠ key) (hneI : "i" ≠ key) (j : Nat) :
    lookupValue (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings key =
      lookupValue st.bindings key :=
  ClimbLoop.foldLoop_preserves_lookup "i" key SegmentLayer3CopyCells.wotsOuterStep hneI
    (fun s => SegmentLayer3CopyCells.wotsOuterStep_preserves_lookup_of_ne s key
      hneDigit hneSteps hneVal hneChainBase hneStep)
    st 0 j

/-- Frame lemma: the seed cell `0x00` keeps its entry value through every prefix
`j ≤ 43` of the WOTS-outer fold. -/
theorem wotsOuterFold_preserves_seed_cell
    (st : RuntimeState) (j : Nat) (hj : j ≤ 43) :
    ((foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world.memory 0x00).val =
      (st.world.memory 0x00).val :=
  ClimbLoop.foldLoop_preserves_memory_val_range "i"
    SegmentLayer3CopyCells.wotsOuterStep 0x00 (fun i => i < 43)
    (fun s idx hidx =>
      SegmentLayer3CopyCells.wotsOuterStep_preserves_memory_zero_of_i
        { s with bindings := bindValue s.bindings "i" (wordNormalize idx) } idx hidx
        (MemoryKit.lookupValue_bindValue_self s.bindings "i" (wordNormalize idx)))
    st 0 j (fun i _ hi => by omega)

/-- Compact entry-state record for the C13 WOTS-outer loop: the seed cell and the
three loop-invariant bindings at the loop's start state.  These four scalar facts
replace the four universally-quantified prefix invariants consumed downstream. -/
structure C13WotsOuterEntry (pkSeed : Bytes) (st : RuntimeState)
    (digest adrs wotsPtr : Nat) : Prop where
  seed0 : (st.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed
  d0 : lookupValue st.bindings "d" = digest
  adrs0 : lookupValue st.bindings "wotsAdrs" = adrs
  wptr0 : lookupValue st.bindings "wotsPtr" = wotsPtr

namespace C13WotsOuterEntry

variable {pkSeed : Bytes} {st : RuntimeState} {digest adrs wotsPtr : Nat}

/-- Seed cell invariant at every prefix `j < 43`, from the entry record. -/
theorem hSeed (e : C13WotsOuterEntry pkSeed st digest adrs wotsPtr)
    (j : Nat) (hj : j < 43) :
    ((foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [wotsOuterFold_preserves_seed_cell st j (by omega), e.seed0]

/-- `d` binding invariant at every prefix `j < 43`, from the entry record. -/
theorem hD (e : C13WotsOuterEntry pkSeed st digest adrs wotsPtr)
    (j : Nat) (_hj : j < 43) :
    lookupValue (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings "d" =
      digest := by
  rw [wotsOuterFold_preserves_binding st "d"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j, e.d0]

/-- `wotsAdrs` binding invariant at every prefix `j < 43`, from the entry record. -/
theorem hAdrs (e : C13WotsOuterEntry pkSeed st digest adrs wotsPtr)
    (j : Nat) (_hj : j < 43) :
    lookupValue (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
        "wotsAdrs" = adrs := by
  rw [wotsOuterFold_preserves_binding st "wotsAdrs"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j, e.adrs0]

/-- `wotsPtr` binding invariant at every prefix `j < 43`, from the entry record. -/
theorem hWPtr (e : C13WotsOuterEntry pkSeed st digest adrs wotsPtr)
    (j : Nat) (_hj : j < 43) :
    lookupValue (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
        "wotsPtr" = wotsPtr := by
  rw [wotsOuterFold_preserves_binding st "wotsPtr"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j, e.wptr0]

end C13WotsOuterEntry

#print axioms wotsOuterFold_preserves_binding
#print axioms wotsOuterFold_preserves_seed_cell
#print axioms C13WotsOuterEntry.hSeed

end SphincsMinusVerifiers
