/-
  SegmentS4ForsDataObligations — standalone reductions for the remaining FORS
  *data* obligations of `C13SeedNamedAcceptGuardedPkRootSizeLeafObligations`
  (`SegmentAcceptSpec`).

  Two axiom-clean bridge bricks, each phrased exactly against the structure's
  field shapes:

  * `hLeaf_of_stepMerkle_seed_frame` reduces the `hLeaf` field (one FORS
    leaf-step preserves the public-seed cell `mem[0x00]`, for every `idx < 6`)
    to a single *unconditional* per-step `stepMerkle` seed-cell frame for the
    inner FORS Merkle climb.  This is the cleanest residual: it isolates the
    whole FORS leaf seed-frame down to the one branchless Merkle swap step.

  * `hmRlo_of_afterFors_root_slots` reduces the `hmRlo` field (the six ordinary
    FORS root cells `0x80 + 32*j`, `j < 6`, after `forsFinalizePreCopyStep`) to
    the FORS outer-loop root-slot correspondence already holding at `afterFors`:
    the pre-copy finalize prefix is a frame over those six source slots, so the
    substantive obligation is purely the `afterFors` reconstruction.

  These are standalone theorems.  They touch neither `execC13` nor
  `c13_refines_byte_spec`; they introduce no `axiom`, no `sorry`, and no
  `native_decide`.  See `STRATEGY.md` (Layer 2/S4, and the soundness rule).
-/

import SphincsMinusVerifiers.SegmentAcceptSpec
import SphincsMinusVerifiers.SegmentS4ForsMerkleFrame
import SphincsMinusVerifiers.SegmentS4Finalize

namespace SphincsMinusVerifiers.SegmentS4ForsDataObligations

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.CurrentNodeFrame
open SphincsMinusVerifierSpec
open SphincsMinusVerifierSpec.C13Concrete

/-- **`hLeaf` reduction.**  The `hLeaf` obligation of
`C13SeedNamedAcceptGuardedPkRootSizeLeafObligations` reduces to an
*unconditional* per-step `stepMerkle` seed-cell frame for the FORS inner Merkle
climb.  Given that every `stepMerkle` iteration preserves the public-seed cell
`mem[0x00]` (the branchless Merkle swap only ever writes the scratch address slot
`0x20` and the parity-determined child slots `{0x40, 0x60}`), each FORS leaf-step
iteration with `idx < 6` preserves it too.

The remaining proof obligation is therefore the single hypothesis `hstep`: one
branchless Merkle swap step never clobbers `mem[0x00]`. -/
theorem hLeaf_of_stepMerkle_seed_frame
    (hstep : ∀ (s : RuntimeState) (hidx : Nat),
      ((SphincsMinusVerifiers.ClimbKit.stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val := by
  intro s idx hidx
  have hi : lookupValue (bindValue s.bindings "i" (wordNormalize idx)) "i" = idx := by
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (lt_trans hidx (by decide))]
  exact SphincsMinusVerifiers.SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) } idx hidx hi hstep

/-- **`hmRlo` reduction.**  The `hmRlo` obligation reduces to the FORS
outer-loop root-slot correspondence at `afterFors`.  The pre-copy finalize prefix
(`forsFinalizePreCopyStep`) only writes the scratch slots `0x20`/`0x40` and the
forced-zero-leaf slot `0x140`; it preserves each of the six ordinary FORS root
source slots `0x80 + 32*j` (`j < 6`).  Hence if `afterFors` already places
`forsAllRootsC13[j]` in those slots, so does the post-finalize state.

The remaining substantive obligation is therefore `hAfter`: the FORS outer
double-loop reconstructs `forsAllRootsC13[j]` into the source slot `0x80 + 32*j`.
(The seventh root `j = 6` at slot `0x140` is *not* a frame — it is overwritten by
the forced-zero leaf hash and is the separate `hmRlast` obligation.) -/
theorem hmRlo_of_afterFors_root_slots
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hAfter : ∀ j, (h : j < 6) →
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega)) :
    ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega) := by
  intro j hj
  rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_preserves_root_source_slot
    (afterFors (mkC13State pkSeed pkRoot message sig)) j hj]
  exact hAfter j hj

#print axioms hLeaf_of_stepMerkle_seed_frame
#print axioms hmRlo_of_afterFors_root_slots

end SphincsMinusVerifiers.SegmentS4ForsDataObligations
