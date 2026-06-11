# Axiom Inventory

Status date: 2026-06-08

This file records the axiom status relevant to the C13/C12
MODEL-EXEC-BRIDGE work.  The target state is defined by
`SphincsMinusVerifiers/STRATEGY.md` section 6.

## Bridge Axioms

- `c13_refines_byte_spec`: still an axiom.
  This is the active C13 MODEL-EXEC-BRIDGE gap.  The intended safe integration
  rule is that this remains an axiom only while exported `execC13` is opaque, and
  the theorem replacement lands atomically with any concrete exported runner.
  The current branch is in that shape: exported `execC13` is opaque, and the
  standalone concrete bridge reducers target internal `execC13Concrete`.

- `c12_refines_byte_spec`: still out of scope until C13 lands.  The early C12
  model-shape word-alignment check has been performed and did not find the
  SHA-2-style packed sub-word write blocker, but this adds no theorem and does
  not change the C12 bridge axiom status.

- SHA-2 bridge axioms: out of scope for this strategy.  SHA-2 remains blocked on
  byte-addressed memory modeling.

## Primitive Axioms

- `c13Primitives`: no longer an axiom in `Proofs.lean`.
  It is defined as `C13Concrete.c13PrimitivesConcrete`.

- C12 primitives are not certified by this C13 pass.

## Residual Assembly Axioms (C13 WOTS-PK + C12 currentNode)

Status: **accepted as minimal honest assembly obligations** (decision 2026-06-08,
option (b)). These are distinct from the MODEL-EXEC-BRIDGE bridge axioms above.
Each is a *concrete-state instantiation* obligation: it pins an already-verified
generic closure to a specific runtime state that is built on `SegmentLayer3`
(`afterDigit` / `beforeWotsPk` / `stepLayer`). The generic mathematical content is
already proven **under the 10 GB build cap**, axiom-clean, in
`C13WotsPkKeccak.lean` (and `C13ChainCells.lean` / `C13WotsOuterInputs.lean`, which
import only the light `SegmentLayer3CopyCells`, peak ~1.6 GB). What remains for each
axiom is solely the wiring of that generic lemma to the concrete state.

**Why these are not discharged here.** Discharging any of them is an edit to
`Proofs.lean` and/or requires `SegmentLayer3.lean`; both compile as single modules at
~48 GB RSS on this 62 GB host (OOM above the cap — empirically kernel-OOM-killed at
~48 GB, and ~21 GB under the 10 GB probe). The on-disk `SegmentLayer3.olean` is also
genuinely stale (built 2026-06-06, source changed 2026-06-07 by commit c4f2ae8), so it
cannot be soundly reused — any import forces an over-cap rebuild. Hence no edit to
these two monoliths is verifiable on this host. Discharge needs a one-time pass on a
**>~64 GB machine**; the per-axiom proofs are then short (mostly a one-line `exact` of
the cited verified lemma). Tracked in project memory (`project-sphincs-verity-refinement`).

The 4 primary residual axioms (all in `Proofs.lean`):

- `c13_ok_beforeAuthOff_wotsPk_lightweight_chain_inputs_layer0`: the five-field
  `C13WotsOuterExactInputs` package (seed / `"d"` / `"wotsAdrs"` / `"wotsPtr"` /
  calldata) holds at the concrete layer-0 WOTS-outer entry state
  `c13BeforeWotsPkLightState (c13LayerLoopState0 …)`. Generic consumers verified:
  `c13Layer0_copyFold43_wotsChainsEnd_cells_of_inputs`,
  `c13Layer0_copyFold43_wotsPk_keccak_of_inputs`.

- `c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer1`: the 43 copied
  chain-end cells equal `InitialNodeKeccak.wotsChainsEnd … d.root0 …` at the concrete
  layer-1 entry state `beforeWotsPkWotsPtrFrom (afterDigit (c13LayerLoopState1 …))`.
  Generic: `c13Layer1_copyFold43_wotsChainsEnd_cells_of_inputs` / `_of_entry`.

- `c13_reverted_layer0_beforeAuthOff_wotsPk_lightweight_chain_cells_residual`: the
  reverted-path twin of the layer-0 chain-cells closure. Generic:
  `c13RevertedLayer0_copyFold43_wotsChainsEnd_cells_of_inputs`.

- `c12_layer3_after3_current_node_root_residual`: the deep C12 layers-0→3 MODEL-EXEC
  roundtrip establishing the layer-3 unrolled root as the runtime `"currentNode"`
  seeding layer 4. All downstream C12 layer-4 residuals are already derived as
  theorems from this single axiom (`C12BridgePrep`).

Discharged 2026-06-11 (now theorems in `Proofs.lean`, no big machine needed):

- `c13_beforeWotsPk_memory_zero_eq_lightweight` (cell `0x00`) and
  `c13_beforeWotsPk_memory_0x20_eq_lightweight` (cell `0x20`): via
  `c13_beforeWotsPk_eq_beforeWotsPkFrom` — the historical and lightweight
  cutpoints run the *same* suffix statement list from `afterDigit ls`, so the
  states are equal and the cell framings are rewrites.
- `c13_beforeWotsPk_memory_chain_eq_lightweight` (cells `0x40 + 32*j`): via the
  `beforeWotsPkAfterWotsCopyFrom` factoring (`c13_beforeWotsPkFrom_eq_afterWotsCopy`),
  `copyFold43_copied_slot` / `c13_copyLoop_preserves_out_slot`, and the
  address-store frame `c13_addressStore_preserves_cell`.  Elaboration discipline:
  assembled with `congrArg`/`trans` only; the copy fold enters via `rw [← he]`
  so its start state is never restated (any defeq between two spellings of a
  fold start state whnf-unfolds the fold); `StmtResult.continue.inj` instead of
  the `injection` tactic.
- `c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_of_inputs_layer0`: via the
  verified `c13Layer0_copyFold43_wotsChainsEnd_cells_of_entry`
  (`C13WotsPkKeccak.lean`), with the Entry record obtained from the inputs record
  at `j = 0` through `ClimbLoop.foldLoop_zero`.

## Current Standalone Lemma Footprints

The C13 proof bricks added for the current accept path are standalone and do not
depend on `c13_refines_byte_spec`.  Their expected `#print axioms` footprints
are:

- `C13Concrete` named FORS root/spec mirror facts:
  `[propext, Quot.sound]`.

- `C13Concrete.parseSignatureC13_R`:
  `[propext]`.

- `C13Concrete.parseSignatureC13_shape`:
  `[propext, Classical.choice, Quot.sound]`.

- `C13Concrete.publicKeyOk_c13` and `C13Concrete.parsePublicKey_c13`:
  `[propext]`.

- `C13Concrete.forcedZeroOk_c13_forsIndex_six`:
  `[propext, Quot.sound]`.

- `C13Concrete.hMsgC13_forsIndex_six`:
  `[propext, Quot.sound]`.

- `C13Concrete.hash16OfWord_size`:
  `[propext]`.

- `C13Concrete.forsPkFromSigC13_size`,
  `C13Concrete.wotsPkFromSigC13_size`,
  `C13Concrete.xmssRootFromSigC13_size`,
  `C13Concrete.foldHypertreeAux_c13_ok_root_size`,
  `C13Concrete.foldHypertree_c13_ok_root_size`, and
  `C13Concrete.foldHypertree_c13_ok_root_size_of_fors`:
  `[propext, Quot.sound]`.

- `C13Concrete.CanonicalHash16` and
  `C13Concrete.hash16OfWord_canonical`:
  `[propext]`.

- `C13Concrete.forsPkFromSigC13_canonical`,
  `C13Concrete.wotsPkFromSigC13_canonical`,
  `C13Concrete.xmssRootFromSigC13_canonical`,
  `C13Concrete.foldHypertreeAux_c13_ok_root_canonical`,
  `C13Concrete.foldHypertree_c13_ok_root_canonical`, and
  `C13Concrete.foldHypertree_c13_ok_root_canonical_of_fors`:
  `[propext, Quot.sound]`.

- `SegmentS3.nat_land_low19` and `SegmentS3.s3Guard_eq_forsIndex6`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentLayer3.beforeDigest_preserves_memory_zero`,
  `SegmentLayer3.beforeDigest_memory_0x20_eq_of_wotsAdrs`,
  `SegmentLayer3.beforeDigest_memory_0x40_eq_currentNode` /
  `SegmentLayer3.beforeDigest_memory_0x40_eq_wordOfHash16`, and
  `SegmentLayer3.beforeDigest_memory_0x60_eq_of_count`, plus
  `SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch`:
  `[propext, Classical.choice, Quot.sound]`.

- `CurrentNodeFrame` seed/FORS-compression frame adapters:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec` final accept adapters and
  `C13SeedNamedAcceptObligations` / `C13SeedNamedAcceptDataObligations` /
  `C13SeedNamedAcceptParsedObligations` /
  `C13SeedNamedAcceptGuardedLayerObligations` /
  `C13SeedNamedAcceptGuardedObligations`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.hash16OfWord_beq_eq_decide`,
  `SegmentAcceptSpec.byteRoot_beq_eq_decide_of_wordOfHash16_roundtrip`, and
  `SegmentAcceptSpec.wordCmp_of_wordOfHash16_roundtrip`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.uint8_toNat_ofNat`:
  `[propext]`.

- `SegmentAcceptSpec.base256_digit_append`,
  `SegmentAcceptSpec.highDigitsFold_eq_mod`,
  `SegmentAcceptSpec.highHalf_mod_digit`,
  `SegmentAcceptSpec.hash16OfWord_wordOfHash16_hash16OfWord`,
  `SegmentAcceptSpec.baToNatBE_hash16OfWord`,
  `SegmentAcceptSpec.wordOfHash16_hash16OfWord_highHalf`,
  `SegmentAcceptSpec.wordOfHash16_hash16OfWord_maskN_of_lt`,
  `SegmentAcceptSpec.forsPkWordC13_roundtrip`,
  `SegmentAcceptSpec.hash16OfWord_wordOfHash16_of_canonical`, and
  `SegmentAcceptSpec.specRoot_roundtrip_of_c13_fors_fold`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.base256_digit_decomp`,
  `SegmentAcceptSpec.base256_uint8_fold_lt`,
  `SegmentAcceptSpec.base256_fold_digit_of_list`,
  `SegmentAcceptSpec.baToNatBE_lt_of_size`, and
  `SegmentAcceptSpec.hash16OfWord_wordOfHash16_of_size`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.base256_uint8_fold_init`:
  `[propext]`.

- `SegmentAcceptSpec.baToNatBE_eq_data_toList`:
  `[propext, Quot.sound]`.

- `SegmentAcceptSpec.c13_sig_length_of_parseSignatureC13`:
  `[propext, Quot.sound]`.

- `SegmentAcceptSpec.c13_s3Guard_of_parse_forcedZero`:
  `[propext, Classical.choice, Quot.sound]`.

- `ClimbLoopGuarded.allGuardsPass_of_rel`:
  `[propext]`.

- `ClimbMemFrameMerkle.address_assembly_eq`:
  `[propext, Classical.choice, Quot.sound]`.

- `ClimbMemFrameMerkle.merkleFold_preserves_memory_val_of_step`,
  `ClimbMemFrameMerkle.merkleFold_preserves_memory_val_bound`,
  `ClimbMemFrameMerkle.merkleFold_preserves_memory_val_range`,
  `ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_of_step`,
  `ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_bound`, and
  `ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_range`:
  `[propext, Classical.choice, Quot.sound]`.

- `ClimbMemFrameMerkle.stepMerkle_mem_zero_of_parity` and
  `ClimbMemFrameMerkle.stepMerkle_mem_zero_val_of_parity`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentS4ForsMerkleFrame.stepMerkle_preserves_seed_slot_of_s4_eval`,
  `SegmentS4ForsMerkleFrame.forsLeafInner_preserves_seed_slot_bound_of_s4_eval`,
  `SegmentS4ForsMerkleFrame.s4_address_assembly_eval_exists`,
  `SegmentS4ForsMerkleFrame.forsLeafInner_preserves_seed_slot_bound_of_step`,
  `SegmentS4ForsMerkleFrame.forsLeafInner_preserves_seed_slot_range_of_step`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound`, and
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_range_of_merkle_step_range`,
  `SegmentS4ForsMerkleFrame.execForsOuter_preserves_seed_slot_range_of_merkle_step_bound`, and
  `SegmentS4ForsMerkleFrame.execForsOuter_preserves_seed_slot_range_of_merkle_step_range`, and
  `SegmentS4ForsMerkleFrame.execForsOuter_preserves_seed_slot_range_of_s4_eval`:
  `[propext, Classical.choice, Quot.sound]`.

- `MemoryFrame.execStmt_letVar_preserves_memory_val`,
  `MemoryFrame.execStmt_assignVar_preserves_memory_val`,
  `MemoryFrame.execStmt_mstore_preserves_memory_val`, and
  `MemoryFrame.execStmtList_preserves_memory_val`:
  `[propext, Classical.choice, Quot.sound]`.

- `MemoryFrame.execForEachLoop_preserves_memory_val`:
  `[propext]`.

- `MemoryFrame.execForEachLoop_preserves_memory_val_bound`:
  `[propext]`.

- `MemoryFrame.execForEachLoop_preserves_memory_val_range`:
  `[propext, Quot.sound]`.

- `MemoryFrame.execStmt_forEach_preserves_memory_val`:
  `[propext, Classical.choice, Quot.sound]`.

- `MemoryFrame.execStmt_forEach_preserves_memory_val_bound` and
  `MemoryFrame.execStmt_forEach_preserves_memory_val_range`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentS4Fors.forsLeafBody_eq_segments`:
  no axioms.

- `SegmentS4Fors.execForsLeafSetup`,
  `SegmentS4Fors.forsLeafSetup_preserves_seed_slot`,
  `SegmentS4Fors.forsLeafSetup_preserves_i`,
  `SegmentS4Fors.forsLeafSetupStep_preserves_seed_slot`,
  `SegmentS4Fors.forsLeafSetupStep_preserves_i`,
  `SegmentS4Fors.execForsLeafInner`,
  `SegmentS4Fors.forsLeafInner_preserves_i`,
  `SegmentS4Fors.execForsLeafStore`,
  `SegmentS4Fors.forsLeafStore_preserves_seed_slot_of_offset`,
  `SegmentS4Fors.forsLeafStore_preserves_i`,
  `SegmentS4Fors.forsLeafBody_preserves_i`,
  `SegmentS4Fors.forsLeafStep_preserves_i`,
  `SegmentS4Fors.forsLeafBody_preserves_seed_slot_range_of_inner`,
  `SegmentS4Fors.forsLeafStep_preserves_seed_slot_range_of_inner`,
  `SegmentS4Fors.eval_forsLeafStore_offset`,
  `SegmentS4Fors.forsLeafStore_offset_ne_zero`,
  `SegmentS4Fors.forsLeafStore_preserves_seed_slot_range`,
  `SegmentS4Fors.execForsOuter_preserves_seed_slot_range`,
  `SegmentS4Fors.execForsOuter_preserves_seed_slot_range_six`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.LayerGuardedStep`,
  `SegmentAcceptSpec.layerGuardsPass_of_guarded_step`, and
  `SegmentAcceptSpec.layerStep_of_guarded_step`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.layerStart_of_seed_named_fors_roots_roundtrip` and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_parse`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.C13SeedNamedAcceptGuardedRoundtripObligations` and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_roundtrip_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.C13SeedNamedAcceptGuardedPkRoundtripObligations` and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_roundtrip_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.C13SeedNamedAcceptGuardedPkRootObligations` and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.C13SeedNamedAcceptGuardedPkRootSizeObligations` and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.C13SeedNamedAcceptGuardedPkRootSizeLeafObligations` and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentS4ForsDataObligations.hLeaf_of_stepMerkle_seed_frame` and
  `SegmentS4ForsDataObligations.hmRlo_of_afterFors_root_slots`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentS4ForsDataObligations.evalExpr_bitAnd_literal_modself`,
  `SegmentS4ForsDataObligations.stepMerkle_seed_frame_unconditional`, and
  `SegmentS4ForsDataObligations.hLeaf_discharged`:
  `[propext, Classical.choice, Quot.sound]`.
  The latter two remove the residual `hstep` hypothesis of
  `hLeaf_of_stepMerkle_seed_frame`: `stepMerkle_seed_frame_unconditional` proves a
  single branchless Merkle swap step preserves `mem[0x00]` for *every* state (no
  `pathIdx < 2^256` bound — the parity witness `n := pathIdx % 2^256` lands the
  `and`-selector value exactly), so `hLeaf_discharged` closes `hLeaf` outright.

These are ordinary Lean/meta foundations for the existing development.  The
forbidden dependencies for these standalone bricks are `sorryAx`, the
MODEL-EXEC-BRIDGE axiom, and an opaque-primitives axiom.

## Required Evidence Commands

Run before considering an integration pass complete:

```bash
lake build SphincsMinusVerifiers
```

After final integration, additionally inspect:

```lean
#print axioms c13_refines_spec
```

The final C13 target is no bridge axiom, no `sorryAx`, and no opaque-primitives
axiom in that output.

## 2026-06 Update: Per-layer obligation reductions (C13BridgePrep + SegmentLayer3)

- Guard obligations (hGuard0/hGuard1) reduced to digitSum data facts via layer0/1_guard_discharged (using the existing layerGuard_of_afterDigit_digitSum_eq from SegmentLayer3).
- CurrentNode obligations (hCurrent0/hCurrent1) reduced via layer0/1_currentNode_discharged, using stepLayer_currentNode_eq_merkleNode + layer merkle climb data supplier (hauth + frozen calldata + merkleClimbData_of_frozenCalldata pattern).
- The two-step observed theorems and allGuardsPass construction updated to supply data facts instead of executable guards.
- This shrinks the C13SeedNamedAcceptConcreteLayerCurrentNodeTwoStepObligations surface.
- Same pattern to be propagated to Proofs.lean and C12 work.
- Target: the ..._two_step_obligations theorem no longer takes full executable layer obligations as parameters; higher bridges become thinner.
- Audit: only foundational + explicitly accepted low-level assembly facts expected in final #print axioms for the observed bridges.
