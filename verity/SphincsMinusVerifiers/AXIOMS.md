# Axiom Inventory

Status date: 2026-06-02

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

- `C13Concrete.parseSignatureC13_layers_length`:
  `[propext]`.

- `C13Concrete.parseSignatureC13_fors_sk_getElem?`:
  `[propext]`.

- `C13Concrete.parseSignatureC13_fors_authPath_getD_getElem?`:
  `[propext]`.

- `C13Concrete.publicKeyOk_c13` and `C13Concrete.parsePublicKey_c13`:
  `[propext]`.

- `C13Concrete.publicKeyOk_c13_does_not_imply_pkRoot_size`:
  `[propext]`.  This is a formal counterexample showing `pkRoot.size = 16`
  cannot be derived from C13 public-key well-formedness alone.

- `C13Concrete.publicKeyOk_c13_does_not_imply_pkSeed_size`:
  `[propext]`.  This is the matching formal counterexample for
  `pkSeed.size = 16`.

- `C13Concrete.parsePublicKey_c13_does_not_imply_pkRoot_size`:
  `[propext]`.  This is a formal counterexample showing `pkRoot.size = 16`
  cannot be derived from C13 byte-level public-key parsing alone.

- `C13Concrete.parsePublicKey_c13_does_not_imply_pkSeed_size`:
  `[propext]`.  This is the matching formal counterexample for
  `pkSeed.size = 16`.

- `C13Concrete.forcedZeroOk_c13_forsIndex_six`:
  `[propext, Quot.sound]`.

- `C13Concrete.hMsgC13_forsIndex_six`:
  `[propext, Quot.sound]`.

- `C13Concrete.hMsgC13_forsIndex_getD_eq`,
  `C13Concrete.hMsgC13_forsIndex_getD_lt`,
  `C13Concrete.adrsForsLeaf_lt_of_normal_idx_lt`, and
  `C13Concrete.adrsForsLeaf_hMsgC13_normal_lt`:
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

- `C13Concrete.wotsDigitSum_fold_le`,
  `C13Concrete.wotsDigitSum_le_301`,
  `C13Concrete.wotsDigitSum_lt_uint256`, and
  `C13Concrete.wotsGrindingFailsC13_false_digitSum`:
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

- `StateFrame` selector/calldata statement/list/loop frame lemmas:
  `[propext, Classical.choice, Quot.sound]` for statement/list adapters, and
  `[propext]` for the pure `foldLoop` adapter.

- `ClimbLoop.foldLoop_append`:
  `[propext, Quot.sound]`.

- `ClimbStepSpec.forsTreeBase_node_address`:
  `[propext]`.

- `ClimbStepSpec.forsClimb_eq_xmssClimb`:
  `[propext, Quot.sound]`.

- `ClimbMemFrameMerkle.forsClimb_model_node` and
  `ClimbMemFrameMerkle.forsClimbFrame_model_node`:
  `[propext, Classical.choice, Quot.sound]`.

- `ClimbMemFrameMerkle.MerkleClimbRawRel` projection/welding facts:
  `.intro`, `.idx`, `.node`, `.node_norm`, and `.toRel` are `[propext]`;
  `MerkleClimbRawRel_of_pair` is `[propext, Quot.sound]`.

- `ClimbMemFrameMerkle.merkleClimbRaw_foldLoop_correspondence` and
  `ClimbMemFrameMerkle.xmssClimbRaw_model_node`:
  `[propext, Classical.choice, Quot.sound]`.

- `ClimbMemFrameMerkle.fors_climb_data_range_getD`:
  `[propext, Classical.choice, Quot.sound]`.

- `CurrentNodeFrame` seed/static-frame/FORS-compression frame adapters, including
  `s2Step_preserves_sig_data_offset`, `afterS2_sig_data_offset_mkC13State`,
  `afterS3_sigBase_mkC13State`, `afterFors_sigBase_mkC13State`,
  `s2Step_preserves_selector_calldata`,
  `afterS2_selector_calldata_mkC13State`,
  `afterS3_selector_calldata_mkC13State`,
  `afterFors_selector_calldata_mkC13State`,
  `forsOuterPrefixState`,
  `forsOuterLeafState`,
  `forsOuterPrefix_sigBase_mkC13State`,
  `forsOuterPrefix_selector_calldata_mkC13State`,
  `forsOuterPrefix_leafSetupFacts_mkC13State`,
  `forsOuterLeafState_setupFacts_mkC13State`,
  `forsLeafStep_preserves_seed_slot_of_mkC13State_prefix`,
  `forsLeafStep_preserves_root_cell_ne_of_mkC13State_prefix`,
  `forsOuterPrefix_root_cell_succ_ne_mkC13State`,
  `forsOuterPrefix_root_cell_suffix_mkC13State`,
  `forsOuterPrefix_root_cell_iteration_node_mkC13State`,
  `afterFors_eq_forsOuterPrefixState_mkC13State`,
  `forsOuterPrefix_seed_slot_mkC13State`,
  `afterFors_seed_slot_mkC13State`,
  `normalRootCell_eq_of_outer_iteration_node`,
  `normalRootCells_eq_forsAllRootsC13_of_iteration_nodes`,
  `normalRootCell_eq_of_fors_frozen_calldata_node`,
  `normalRootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes`,
  `normalRootCell_eq_of_mkC13State_iteration_node`,
  `normalRootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes`,
  `forsAuthCdAt`,
  `forsOuterLeafState_node_eq_forsAllRootsC13_of_eval_parse`,
  `forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_eval_parse`,
  `forsLeafAddress_eval_eq_adrsForsLeaf`,
  `forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_eval_parse`,
  `afterS3_dVal_mkC13State`,
  `forsOuterPrefix_dVal_mkC13State`,
  `forsOuterLeafState_dVal_mkC13State`,
  `forsOuterLeafState_treeIdx_eval_eq_hMsg_parse`,
  `forsSecret_eval_eq_wordOfHash16_parse`,
  `forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_secret_parse`,
  `forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_tree_secret_parse`,
  `forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_tree_secret_parse_concrete`,
  `SegmentS4ForsMerkleFrame.forsLeafSetupStep_fors_frozen_calldata_site`,
  `SegmentS4ForsMerkleFrame.forsLeafSetupStep_forsFrozenSite`,
  `SegmentS4ForsMerkleFrame.forsLeafSetupStep_initial_forsClimbRel_of_eval`,
  `SegmentS4ForsMerkleFrame.forsLeafSetupStep_initial_forsClimbFrame_of_eval_site`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimb_of_eval`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsAllRootsC13_getElem_of_eval`,
  `SegmentS4ForsMerkleFrame.stepMerkle_preserves_forsFrozenSite`,
  `SegmentS4ForsMerkleFrame.foldLoop_preserves_forsFrozenSite_range`,
  `SegmentS4ForsMerkleFrame.foldLoop_preserves_seed_slot_of_forsFrozenSite_range`,
  `SegmentS4ForsMerkleFrame.foldLoop_preserves_root_cell_of_forsFrozenSite_range`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_preserves_seed_slot_of_forsFrozenSite`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_preserves_root_cell_of_forsFrozenSite`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_of_forsFrozenSetup`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_root_cell_ne_of_forsFrozenSetup`,
	  `finalSecret_eval_eq_wordOfHash16`,
	  `forcedRootCell_eq_forsAllRootsC13_of_parse`, and
	  `forcedRootCell_eq_forsAllRootsC13_of_parse_calldata`,
	  `forcedRootCell_eq_forsAllRootsC13_of_parse_static`, and
	  `forcedRootCell_eq_forsAllRootsC13_of_parse_range_seed`,
	  `forcedRootCell_eq_forsAllRootsC13_of_parse_concrete`,
	  `rootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes_and_parse_range_seed`,
	  `rootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes_and_parse`,
	  `rootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes_and_parse`,
	  `rootCells_eq_forsAllRootsC13_of_hMsg_parse_concrete`,
	  `forsPkCompressWord_eq_of_afterFors_concrete_mkC13State_six_plus_last`,
	  `stepLayer_currentNodeRel_of_merkleNode`,
	  `afterLayer_currentNode_of_step`,
	  `afterLayer_currentNode_of_step_range`,
	  `afterLayer_currentNode_of_forsPk_step`,
	  `afterLayer_currentNode_wordOfHash16_of_forsPk_step`, and
	  `afterLayer_currentNode_wordOfHash16_of_forsPk_step_range`:
	  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec` final accept adapters and
  `C13SeedNamedAcceptObligations` / `C13SeedNamedAcceptDataObligations` /
  `C13SeedNamedAcceptParsedObligations` /
  `C13SeedNamedAcceptGuardedLayerObligations` /
  `C13SeedNamedAcceptGuardedObligations` /
	  `C13SeedNamedAcceptConcreteLayerObligations` /
	  `no_concrete_layer_obligations_of_parse` /
	  `seed_named_pk_root_size_obligations_of_concrete_layer_obligations` /
	  `accept_path_returns_verifyParsed_bool_from_layer_step_range` /
	  `accept_path_returns_verifyParsed_bool_from_concrete_layer_obligations_of_bytes`:
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

- `SegmentRejectSpec.mkC13State_lookup_sigLength`,
  `SegmentRejectSpec.c13_body_reverts_on_bad_length`,
  `SegmentRejectSpec.c13_verifyBytes_none_on_bad_length`,
  `SegmentRejectSpec.c13_revert_on_bad_length`,
  `SegmentRejectSpec.c13_body_reverts_on_forced_zero`,
  `SegmentRejectSpec.c13_revert_on_forced_zero` (the low-level form takes the
  spec-side forced-zero connection as a surfaced hypothesis),
  `SegmentRejectSpec.c13_verifyBytes_none_on_forced_zero_of_parse`,
  `SegmentRejectSpec.c13_forcedZero_false_of_parse_s3Guard`, and
  `SegmentRejectSpec.c13_revert_on_forced_zero_of_parse`:
  `[propext, Classical.choice, Quot.sound]`.

- `ClimbLoopGuarded.allGuardsPass_of_rel`:
  `[propext]`.

- `ClimbLoopGuarded.allGuardsPass_of_rel_range`:
  `[propext, Quot.sound]`.

- `ClimbMemFrameMerkle.address_assembly_eq`:
  `[propext, Classical.choice, Quot.sound]`.

- `ClimbMemFrameMerkle.merkleFold_preserves_memory_val_of_step`,
  `ClimbMemFrameMerkle.merkleFold_preserves_memory_val_bound`,
  `ClimbMemFrameMerkle.merkleFold_preserves_memory_val_range`,
  `ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_of_step`,
  `ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_bound`, and
  `ClimbMemFrameMerkle.execStmt_forEach_h_merkleClimb_preserves_memory_val_range`:
  `[propext, Classical.choice, Quot.sound]`.

- `ClimbMemFrameMerkle.stepMerkle_mem_val_of_ne`,
  `ClimbMemFrameMerkle.stepMerkle_mem_zero_of_parity`, and
  `ClimbMemFrameMerkle.stepMerkle_mem_zero_val_of_parity`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentS4ForsMerkleFrame.stepMerkle_preserves_seed_slot_of_s4_eval`,
  `SegmentS4ForsMerkleFrame.stepMerkle_forsFrame_hstep_of_s4_data`,
  `SegmentS4ForsMerkleFrame.stepMerkle_forsFrame_hstep_of_fors_frozen_calldata`,
  `SegmentS4ForsMerkleFrame.forsLeafInner_preserves_seed_slot_bound_of_s4_eval`,
  `SegmentS4ForsMerkleFrame.s4_address_assembly_eval_exists`,
  `SegmentS4ForsMerkleFrame.s4_eval_site_of_frozen_calldata`,
  `SegmentS4ForsMerkleFrame.s4_eval_site_of_fors_frozen_calldata`,
  `SegmentS4ForsMerkleFrame.forsLeafSetupStep_initial_forsClimbFrame_of_eval_site`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site_range`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site_range_path_bound`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimbFrame_of_fors_frozen_calldata`,
  `SegmentS4ForsMerkleFrame.stepMerkle_preserves_seed_slot_of_fors_frozen_calldata`,
  `SegmentS4ForsMerkleFrame.stepMerkle_preserves_root_cell_of_fors_frozen_calldata`,
  `SegmentS4ForsMerkleFrame.forsLeafInner_preserves_seed_slot_bound_of_step`,
  `SegmentS4ForsMerkleFrame.forsLeafInner_preserves_memory_val_bound_of_step`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_root_cell_range_ne_of_inner_step`,
  `SegmentS4ForsMerkleFrame.stepMerkle_preserves_root_cell_of_s4_eval`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_root_cell_range_ne_of_s4_eval`,
  `SegmentS4ForsMerkleFrame.forsOuter_root_cell_eq_iteration_node_of_s4_eval`,
  `SegmentS4ForsMerkleFrame.forsLeafInner_preserves_seed_slot_range_of_step`,
  `SegmentS4ForsMerkleFrame.foldLoop_preserves_forsFrozenSite_range`,
  `SegmentS4ForsMerkleFrame.foldLoop_preserves_seed_slot_of_forsFrozenSite_range`,
  `SegmentS4ForsMerkleFrame.foldLoop_preserves_root_cell_of_forsFrozenSite_range`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_preserves_seed_slot_of_forsFrozenSite`,
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_preserves_root_cell_of_forsFrozenSite`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_of_forsFrozenSetup`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_root_cell_ne_of_forsFrozenSetup`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound`, and
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_range_of_merkle_step_range`,
  `SegmentS4ForsMerkleFrame.execForsOuter_preserves_seed_slot_range_of_merkle_step_bound`, and
  `SegmentS4ForsMerkleFrame.execForsOuter_preserves_seed_slot_range_of_merkle_step_range`, and
  `SegmentS4ForsMerkleFrame.execForsOuter_preserves_seed_slot_range_of_s4_eval`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_root_cell_range_ne_of_fors_frozen_calldata`,
  `SegmentS4ForsMerkleFrame.forsOuter_root_cell_eq_iteration_node_of_fors_frozen_calldata`,
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_range_of_fors_frozen_calldata`, and
  `SegmentS4ForsMerkleFrame.execForsOuter_preserves_seed_slot_range_of_fors_frozen_calldata`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentS4Finalize.forsFinalizePreCopyStep_forced_root_cell`:
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

- `ClimbLoop.foldLoop_memory_val_eq_step_at_of_suffix_preserves`:
  `[propext, Quot.sound]`.

- `SegmentS4Fors.forsLeafBody_eq_segments`:
  no axioms.

- `SegmentS4Fors.execForsLeafSetup`,
  `SegmentS4Fors.forsLeafSetup_preserves_seed_slot`,
  `SegmentS4Fors.forsLeafSetup_preserves_root_cell_range`,
  `SegmentS4Fors.forsLeafSetup_preserves_i`,
  `SegmentS4Fors.forsLeafSetupStep_preserves_seed_slot`,
  `SegmentS4Fors.forsLeafSetupStep_preserves_root_cell_range`,
  `SegmentS4Fors.forsLeafSetupStep_preserves_i`,
  `SegmentS4Fors.forsLeafSetup_preserves_sigBase`,
  `SegmentS4Fors.forsLeafSetupStep_preserves_sigBase`,
  `SegmentS4Fors.forsLeafSetup_preserves_dVal`,
  `SegmentS4Fors.forsLeafSetupStep_preserves_dVal`,
  `SegmentS4Fors.forsLeafStep_preserves_dVal`,
	  `SegmentS4Fors.forsLeafSetupStep_authPtr_eq_sigDataOffset`,
	  `SegmentS4Fors.forsLeafSetupStep_pathIdx_lt`,
	  `SegmentS4Fors.forsLeafSetupStep_pathIdx_eq_of_eval`,
	  `SegmentS4Fors.forsTreeAdrsBase_eval_eq`,
	  `SegmentS4Fors.forsLeafSetupStep_treeAdrsBase_exists_lt`,
	  `SegmentS4Fors.forsLeafSetupStep_treeAdrsBase_eq_of_i`,
	  `SegmentS4Fors.forsLeafSetupStep_node_eq_spec_of_eval`,
	  `SegmentS4Fors.forsLeafSetupStep_preserves_selector_calldata`,
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
  `SegmentS4Fors.forsLeafStore_root_cell_range`,
  `SegmentS4Fors.forsLeafStore_preserves_root_cell_range_ne`,
  `SegmentS4Fors.forsLeafStep_root_cell_range`,
  `SegmentS4Fors.forsLeafBody_preserves_root_cell_range_ne_of_inner`,
  `SegmentS4Fors.forsLeafStep_preserves_root_cell_range_ne_of_inner`,
  `SegmentS4Fors.forsOuter_root_cell_eq_iteration_node_of_suffix_preserves`,
  `SegmentS4Fors.execForsOuter_preserves_seed_slot_range`,
  `SegmentS4Fors.execForsOuter_preserves_seed_slot_range_six`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.LayerGuardedStep`,
  `SegmentLayer3.nat_land_low3`,
  `SegmentLayer3.digitSumStep_digitSum_eq`,
  `SegmentLayer3.digitSumStep_preserves_d`,
  `SegmentLayer3.foldLoop_digitSum_eq`,
  `SegmentLayer3.digitSumFold_zero_eq_wotsDigitSum`,
  `SegmentLayer3.beforeWotsDigest_eq`,
  `SegmentLayer3.beforeWotsDigest_seed_slot_eq`,
  `SegmentLayer3.wotsAdrs_eval_eq_adrsWotsHashBase`,
  `SegmentLayer3.beforeWotsDigestAdrsSlot_wotsAdrs_lookup_eq`,
  `SegmentLayer3.beforeWotsDigest_wotsAdrs_slot_eq`,
  `SegmentLayer3.beforeWotsDigest_wotsAdrs_slot_eq_of_lookup`,
  `SegmentLayer3.beforeWotsDigest_currentNode_slot_eq`,
  `SegmentLayer3.beforeWotsDigest_currentNode_slot_eq_of_lookup`,
  `SegmentLayer3.beforeWotsDigest_count_slot_eq`,
  `SegmentLayer3.beforeWotsDigest_count_slot_eq_of_lookup`,
  `SegmentLayer3.countExpr_eval_eq_shifted_calldata`,
  `SegmentLayer3.beforeDigitSum_eq`,
  `SegmentLayer3.beforeDigitSum_digitSum_eq_zero`,
  `SegmentLayer3.beforeDigitSum_d_eq_keccakWords_of_beforeWotsDigest_memory`,
  `SegmentLayer3.beforeDigitSum_d_eq_wotsDigest_of_beforeWotsDigest_memory`,
  `SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_wotsDigest_of_beforeWotsDigest_memory`,
  `SegmentLayer3.afterDigit_eq_foldLoop_digitSum`,
  `SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitSum_d`,
  `SegmentLayer3.layerGuard_of_afterDigit_digitSum_eq`,
  `SegmentLayer3.beforeMerkle_eq`,
  `SegmentLayer3.finalLayerTail_preserves_merkleNode`,
  `SegmentAcceptSpec.c13HypertreeSpecStep_eq_root_of_success`,
  `SegmentAcceptSpec.layerGuardedStep_c13HypertreeSpecStep_of_merkleNode`,
  `SegmentAcceptSpec.stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success`,
  `SegmentAcceptSpec.layerGuardedStep_c13HypertreeSpecStep_of_success`,
  `SegmentAcceptSpec.layerGuardedStep_c13HypertreeSpecStep_of_digitSum_success`,
  `SegmentAcceptSpec.afterMerkle_model_node_of_xmss_frame`,
  `SegmentAcceptSpec.afterMerkle_model_node_of_xmss_frame_c13`,
  `SegmentAcceptSpec.afterMerkle_model_node_raw`,
  `SegmentAcceptSpec.afterMerkle_model_node_raw_c13`,
  `SegmentAcceptSpec.xmssClimb_roundtrip_of_node_roundtrip`,
  `SegmentAcceptSpec.xmssClimb_roundtrip_of_wots_success`,
  `SegmentAcceptSpec.xmssRootFromSigC13_some_eq_hash16OfWord_xmssClimb`,
  `SegmentAcceptSpec.stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb`,
  `SegmentAcceptSpec.stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb_wots_success`,
  `SegmentAcceptSpec.stepLayer_merkleNode_eq_wordOfHash16_root_of_normalized_xmssClimb_wots_success`,
  `SegmentAcceptSpec.stepLayer_merkleNode_norm_eq_wordOfHash16_root_of_xmssClimb_wots_success`,
  `SegmentAcceptSpec.specFold_c13HypertreeSpecStep_eq_of_foldHypertree_ok`,
  `SegmentAcceptSpec.layerGuardsPass_of_guarded_step`, and
  `SegmentAcceptSpec.layerStep_of_guarded_step`,
  `SegmentAcceptSpec.layerGuardsPass_of_c13HypertreeSpecStep_success`, and
  `SegmentAcceptSpec.layerStep_of_c13HypertreeSpecStep_success`,
  `SegmentAcceptSpec.layerGuardsPass_of_c13HypertreeSpecStep_success_range`, and
  `SegmentAcceptSpec.layerGuardsPass_of_c13HypertreeSpecStep_digitSum_success_range`, and
  `SegmentAcceptSpec.layerStep_of_c13HypertreeSpecStep_success_range`:
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

- `SegmentAcceptSpec.C13SeedNamedAcceptGuardedPkRootSizeLeafRootObligations`,
  `SegmentAcceptSpec.seed_named_leaf_obligations_of_leaf_root_obligations`, and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_root_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.C13SeedNamedAcceptGuardedPkRootSizeSiteRootObligations`,
  `SegmentAcceptSpec.seed_named_leaf_root_obligations_of_site_root_obligations`,
  `SegmentAcceptSpec.seed_named_pk_root_size_obligations_of_site_root_obligations`,
  and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_site_root_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.C13SeedNamedAcceptConcreteLayerSiteRootObligations`,
  `SegmentAcceptSpec.site_root_obligations_of_concrete_layer_site_root_obligations`,
  `SegmentAcceptSpec.no_concrete_layer_site_root_obligations_of_parse`,
  and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_concrete_layer_site_root_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

- `SegmentAcceptSpec.C13SeedNamedAcceptConcreteLayerObligations`,
  `SegmentAcceptSpec.C13SeedNamedAcceptConcreteLayerRangeObligations`,
  `SegmentAcceptSpec.C13SeedNamedAcceptConcreteLayerDigitSumRangeObligations`,
  `SegmentAcceptSpec.concrete_layer_range_obligations_of_digitSum_range_obligations`,
  `SegmentAcceptSpec.C13SeedNamedAcceptConcreteLayerDigitCellRangeObligations`,
  `SegmentAcceptSpec.digitSum_range_obligations_of_digit_cell_range_obligations`,
  `SegmentAcceptSpec.seed_named_pk_root_size_obligations_of_concrete_layer_obligations`,
  `SegmentAcceptSpec.no_concrete_layer_obligations_of_parse`,
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_concrete_layer_obligations_of_bytes`, and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_concrete_layer_range_obligations_of_bytes`, and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_concrete_layer_digitSum_range_obligations_of_bytes`, and
  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_concrete_layer_digit_cell_range_obligations_of_bytes`:
  `[propext, Classical.choice, Quot.sound]`.

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
