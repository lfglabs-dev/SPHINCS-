# Axiom Inventory

Status date: 2026-06-01

This file records the axiom status relevant to the C13/C12
MODEL-EXEC-BRIDGE work.  The target state is defined by
`SphincsMinusVerifiers/STRATEGY.md` section 6.

## Bridge Axioms

- `c13_refines_byte_spec`: still an axiom.
  This is the active C13 MODEL-EXEC-BRIDGE gap.  It must remain an axiom until
  the same atomic change also replaces `opaque execC13` with the interpreter
  definition and proves the theorem.

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
