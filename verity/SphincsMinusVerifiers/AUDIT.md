# C13/C12 MODEL-EXEC-BRIDGE Audit

Status date: 2026-06-02

This audit tracks the acceptance criteria from `SphincsMinusVerifiers/STRATEGY.md`
for the C13, then C12, MODEL-EXEC-BRIDGE discharge.  It is intentionally
conservative: partial proof infrastructure is recorded as progress, not as
completion of the bridge.

## Definition-Of-Done Checklist

- `c13Primitives` is concrete: satisfied for C13.
  Evidence: `SphincsMinusVerifiers/Proofs.lean` defines
  `c13Primitives : Primitives := C13Concrete.c13PrimitivesConcrete`.

- `execC13` is concrete and introduced atomically with the bridge theorem: not
  satisfied.
  Evidence: `SphincsMinusVerifiers/Proofs.lean` still has `opaque execC13`.
  This is intentional until `c13_refines_byte_spec` can be proved in the same
  change.

- `c13_refines_byte_spec` is a theorem, not an axiom: not satisfied.
  Evidence: `SphincsMinusVerifiers/Proofs.lean` still has
  `axiom c13_refines_byte_spec`.

- `#print axioms c13_refines_spec` has no bridge axiom: not satisfied yet.
  Current expected evidence still includes the bridge axiom because
  `c13_refines_byte_spec` remains an axiom.

- `lake build SphincsMinusVerifiers` is green: satisfied for the current partial
  proof state.
  Last checked in this worktree after adding the concrete C13 FORS setup-node
  bridge plus the existing outer-prefix setup/root-cell facts, then syncing this
  audit/doc set.

- `AUDIT.md`, `TRUST_ASSUMPTIONS.md`, `AXIOMS.md`, and `README.md` are synced:
  satisfied for the current partial state by these files and the README entries
  for the latest C13 FORS/accept/roundtrip adapters.

- Source-to-model fidelity is recorded as separate and untouched: satisfied.
  See `TRUST_ASSUMPTIONS.md`.

- C12 16-byte truncation word-alignment precheck: satisfied at the model-shape
  level, not yet a C12 bridge proof.
  Evidence: `SphincsMinusVerifiers/Model.lean`'s `c12VerifyBody` represents
  16-byte nodes by `calldataload ... & N_MASK` / `keccak ... & N_MASK` words and
  stores them only at word-aligned scratch/root-array offsets (`0x20`, `0x40`,
  `0x60`, `0x80 + 32*i`, `0x40 + 32*i`, `0x100 + 32*i`, etc.).  It does not use
  the SHA-2 model's packed sub-word stores such as `0x56` or `0x66`.

## Current C13 Proof Surface

The current C13 work is still pre-integration.  It proves standalone bridge
bricks that do not define `execC13` and do not use the bridge axiom:

- named FORS root/spec mirror facts in
  `SphincsMinusVerifierSpec/C13Concrete.lean`;
- C13 parse/forced-zero spec facts in
  `SphincsMinusVerifierSpec/C13Concrete.lean`:
  `parseSignatureC13_R`, `parseSignatureC13_shape`,
  `parseSignatureC13_fors_sk_getElem?`,
  `parseSignatureC13_fors_authPath_getD_getElem?`,
  `publicKeyOk_c13`, `parsePublicKey_c13`,
  `publicKeyOk_c13_does_not_imply_pkRoot_size`,
  `publicKeyOk_c13_does_not_imply_pkSeed_size`,
  `parsePublicKey_c13_does_not_imply_pkRoot_size`,
  `parsePublicKey_c13_does_not_imply_pkSeed_size`,
  `forcedZeroOk_c13_forsIndex_six`, `hMsgC13_forsIndex_six`,
  `hMsgC13_forsIndex_getD_eq`, `hMsgC13_forsIndex_getD_lt`,
  `adrsForsLeaf_lt_of_normal_idx_lt`, and `adrsForsLeaf_hMsgC13_normal_lt`;
- C13 16-byte result-shape facts in
  `SphincsMinusVerifierSpec/C13Concrete.lean`:
  `hash16OfWord_size`, `forsPkFromSigC13_size`,
  `wotsPkFromSigC13_size`, `xmssRootFromSigC13_size`,
  `foldHypertreeAux_c13_ok_root_size`,
  `foldHypertree_c13_ok_root_size`, and
  `foldHypertree_c13_ok_root_size_of_fors`;
- C13 canonical-output facts in
  `SphincsMinusVerifierSpec/C13Concrete.lean`:
  `CanonicalHash16`, `hash16OfWord_canonical`,
  `forsPkFromSigC13_canonical`, `wotsPkFromSigC13_canonical`,
  `xmssRootFromSigC13_canonical`,
  `foldHypertreeAux_c13_ok_root_canonical`,
  `foldHypertree_c13_ok_root_canonical`, and
  `foldHypertree_c13_ok_root_canonical_of_fors`;
- C13 WOTS grinding-target fact in
  `SphincsMinusVerifierSpec/C13Concrete.lean`:
  `wotsDigitSum_fold_le`, `wotsDigitSum_le_301`, and
  `wotsDigitSum_lt_uint256`, which bound the 43 three-bit WOTS digits by
  `301`, plus
  `wotsGrindingFailsC13_false_digitSum`, which derives the concrete digit-sum
  target `208` from `wotsGrindingFails = false`;
- S3 guard arithmetic facts in `SphincsMinusVerifiers/SegmentS3.lean`:
  `nat_land_low19` and `s3Guard_eq_forsIndex6`;
- Layer-3 digit-sum arithmetic facts in
  `SphincsMinusVerifiers/SegmentLayer3.lean`: `nat_land_low3` and
  `digitSumStep_digitSum_eq`, covering one executable digit-sum loop step, plus
  `digitSumStep_preserves_d` and `foldLoop_digitSum_eq`, lifting that step over
  the pure checksum `foldLoop`, and `digitSumFold_zero_eq_wotsDigitSum`, matching
  the 43-step pure fold to the concrete C13 `wotsDigitSum`.  The
  `beforeWotsDigest`/`beforeDigitSum` splits,
  `beforeDigitSum_d_eq_wotsDigest_of_beforeWotsDigest_memory`, and
  `afterDigit_digitSum_eq_wotsDigitSum_wotsDigest_of_beforeWotsDigest_memory`
  expose the exact executable `"d"` and post-prefix `"digitSum"` handoff from a
  four-word WOTS-digest scratch-frame hypothesis; `beforeWotsDigest_seed_slot_eq`
  closes the seed-slot preservation part of that frame;
- seed and FORS-compression frame adapters in
  `SphincsMinusVerifiers/CurrentNodeFrame.lean`;
- forced-root final-secret calldata and parsed-root cell adapters in
  `SphincsMinusVerifiers/CurrentNodeFrame.lean`:
  `finalSecret_eval_eq_wordOfHash16`,
  `forcedRootCell_eq_forsAllRootsC13_of_parse`, and
  `forcedRootCell_eq_forsAllRootsC13_of_parse_calldata`;
- FORS finalize forced-root scratch-cell adapter
  `SegmentS4Finalize.forsFinalizePreCopyStep_forced_root_cell`;
- generic memory-cell frame lemmas in
  `SphincsMinusVerifiers/MemoryFrame.lean`, including the per-statement,
  statement-list, raw `execForEachLoop`, and statement-level `.forEach`
  preservation lifts, plus bounded and range-gated raw `execForEachLoop` and
  statement-level `.forEach` memory-frame variants;
- Merkle-climb memory-frame adapters in
  `SphincsMinusVerifiers/ClimbMemFrameMerkle.lean`, including
  `MerkleClimbRawRel`, `MerkleClimbRawRel.toRel`,
  `MerkleClimbRawRel_of_pair`,
  `merkleClimbRaw_foldLoop_correspondence`, and
  `xmssClimbRaw_model_node` for exact, un-normalized `nodeVar` equality through
  a Merkle fold,
  `stepMerkle_mem_val_of_ne`,
  `stepMerkle_mem_zero_of_parity`,
  `stepMerkle_mem_zero_val_of_parity`,
  `merkleFold_preserves_memory_val_of_step`,
  `merkleFold_preserves_memory_val_bound`,
  `merkleFold_preserves_memory_val_range`, and the statement-level
  `execStmt_forEach_h_merkleClimb_preserves_memory_val_of_step`,
  `execStmt_forEach_h_merkleClimb_preserves_memory_val_bound`, and
  `execStmt_forEach_h_merkleClimb_preserves_memory_val_range`;
- S4/Merkle adapter lemmas in
  `SphincsMinusVerifiers/SegmentS4ForsMerkleFrame.lean`:
  `stepMerkle_forsFrame_hstep_of_s4_data`,
  `stepMerkle_forsFrame_hstep_of_fors_frozen_calldata`,
  `stepMerkle_preserves_seed_slot_of_s4_eval`,
  `forsLeafInner_preserves_seed_slot_bound_of_s4_eval`,
  `s4_address_assembly_eval_exists`,
  `s4_eval_site_of_frozen_calldata`,
  `s4_eval_site_of_fors_frozen_calldata`,
  `stepMerkle_preserves_seed_slot_of_fors_frozen_calldata`,
  `stepMerkle_preserves_root_cell_of_fors_frozen_calldata`,
  `forsLeafInner_preserves_seed_slot_bound_of_step`,
  `forsLeafInner_preserves_memory_val_bound_of_step`,
  `forsLeafStep_preserves_root_cell_range_ne_of_inner_step`,
  `stepMerkle_preserves_root_cell_of_s4_eval`,
  `forsLeafStep_preserves_root_cell_range_ne_of_s4_eval`,
  `forsOuter_root_cell_eq_iteration_node_of_s4_eval`,
  `forsLeafInner_preserves_seed_slot_range_of_step`,
  `forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound`, and
  `forsLeafStep_preserves_seed_slot_range_of_merkle_step_range`,
  `execForsOuter_preserves_seed_slot_range_of_merkle_step_bound`, and
  `execForsOuter_preserves_seed_slot_range_of_merkle_step_range`, and
  `execForsOuter_preserves_seed_slot_range_of_s4_eval`,
  `forsLeafStep_preserves_root_cell_range_ne_of_fors_frozen_calldata`,
  `forsOuter_root_cell_eq_iteration_node_of_fors_frozen_calldata`,
  `forsLeafStep_preserves_seed_slot_range_of_fors_frozen_calldata`, and
  `execForsOuter_preserves_seed_slot_range_of_fors_frozen_calldata`;
- S4 FORS body split plus setup/final-store frame facts in
  `SphincsMinusVerifiers/SegmentS4Fors.lean`:
  `forsLeafBody_eq_segments`, `execForsLeafSetup`,
  `forsLeafSetup_preserves_seed_slot`,
  `forsLeafSetup_preserves_root_cell_range`, `forsLeafSetup_preserves_i`,
  `forsLeafSetupStep_preserves_seed_slot`,
  `forsLeafSetupStep_preserves_root_cell_range`,
  `forsLeafSetupStep_preserves_i`,
  `forsLeafSetup_preserves_sigBase`, `forsLeafSetupStep_preserves_sigBase`,
  `forsLeafSetup_preserves_dVal`, `forsLeafSetupStep_preserves_dVal`,
  `forsLeafStep_preserves_dVal`,
  `forsLeafSetupStep_preserves_selector_calldata`,
  `forsLeafSetupStep_authPtr_eq_sigDataOffset`,
  `forsLeafSetupStep_pathIdx_lt`,
  `forsLeafSetupStep_pathIdx_eq_of_eval`,
  `forsTreeAdrsBase_eval_eq`,
  `forsLeafSetupStep_treeAdrsBase_exists_lt`,
  `forsLeafSetupStep_treeAdrsBase_eq_of_i`,
  `forsLeafSetupStep_node_eq_spec_of_eval`, `execForsLeafInner`,
  `forsLeafInner_preserves_i`,
  `execForsLeafStore`, `forsLeafStore_preserves_seed_slot_of_offset`,
  `forsLeafStore_preserves_i`, `forsLeafBody_preserves_i`,
  `forsLeafStep_preserves_i`,
  `forsLeafBody_preserves_seed_slot_range_of_inner`,
  `forsLeafStep_preserves_seed_slot_range_of_inner`,
  `eval_forsLeafStore_offset`,
  `forsLeafStore_offset_ne_zero`, `forsLeafStore_preserves_seed_slot_range`,
  `forsLeafStore_root_cell_range`,
  `forsLeafStore_preserves_root_cell_range_ne`,
  `forsLeafStep_root_cell_range`,
  `forsLeafBody_preserves_root_cell_range_ne_of_inner`,
  `forsLeafStep_preserves_root_cell_range_ne_of_inner`,
  `execForsOuter_preserves_seed_slot_range`, and
  `execForsOuter_preserves_seed_slot_range_six`;
- final accept-path adapters and the bundled
  `C13SeedNamedAcceptObligations` / `C13SeedNamedAcceptDataObligations` /
  `C13SeedNamedAcceptParsedObligations` /
  `C13SeedNamedAcceptGuardedLayerObligations` /
  `C13SeedNamedAcceptGuardedObligations` /
  `C13SeedNamedAcceptGuardedRoundtripObligations` /
  `C13SeedNamedAcceptGuardedPkRoundtripObligations` /
  `C13SeedNamedAcceptGuardedPkRootObligations` /
  `C13SeedNamedAcceptGuardedPkRootSizeObligations` /
  `C13SeedNamedAcceptGuardedPkRootSizeLeafObligations` /
  `C13SeedNamedAcceptGuardedPkRootSizeLeafRootObligations` /
  `C13SeedNamedAcceptGuardedPkRootSizeSiteRootObligations` /
  `C13SeedNamedAcceptConcreteLayerSiteRootObligations` /
  `C13SeedNamedAcceptConcreteLayerObligations` /
  `C13SeedNamedAcceptConcreteLayerRangeObligations` contracts in
  `SphincsMinusVerifiers/SegmentAcceptSpec.lean`.  The concrete-layer
  all-`Nat` contracts are now formally marked too strong for parsed C13 signatures:
  `no_concrete_layer_site_root_obligations_of_parse` and
  `no_concrete_layer_obligations_of_parse` use
  `parseSignatureC13_layers_length` to refute their all-`idx : Nat` success
  fields at `idx = 2`; the range contract is consumed by
  `accept_path_returns_verifyParsed_bool_from_concrete_layer_range_obligations_of_bytes`;
- concrete C13 per-layer hypertree spec-step adapters in
  `SphincsMinusVerifiers/SegmentAcceptSpec.lean`:
  `c13HypertreeSpecStep_eq_root_of_success`,
  `layerGuardedStep_c13HypertreeSpecStep_of_merkleNode`, and
  `stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success`, plus
  `layerGuardedStep_c13HypertreeSpecStep_of_success`, which packages guard
  facts, successful WOTS/XMSS spec facts, and the post-step `"merkleNode"` word
  equality into `LayerGuardedStep`; `SegmentLayer3.layerGuard_of_afterDigit_digitSum_eq`
  and `layerGuardedStep_c13HypertreeSpecStep_of_digitSum_success` narrow the guard
  side to the concrete `"digitSum" = 208` post-prefix data-cell fact;
  `SegmentLayer3.suffixBeforeMerkle`, `beforeMerkle`, `afterMerkle`, and
  `beforeMerkle_eq` split the layer suffix around the XMSS Merkle climb so the
  remaining `"merkleNode"` proof can target the existing Merkle frame fold state;
  `SegmentLayer3.finalLayerTail_preserves_merkleNode` isolates the final
  `currentNode`/`sigOff` assignment tail as preserving the post-climb
  `"merkleNode"` binding;
  `afterMerkle_model_node_of_xmss_frame` applies the frame-threaded XMSS theorem
  to that split, producing the normalized model node from a materialized XMSS
  frame, and `afterMerkle_model_node_of_xmss_frame_c13` specializes that bridge
  to literal C13 XMSS height `11`; `afterMerkle_model_node_raw` and
  `afterMerkle_model_node_raw_c13` provide the exact post-`afterMerkle`
  `"merkleNode"` lookup equality when callers can supply the raw Merkle climb
  relation; the new
  `xmssRootFromSigC13_some_eq_hash16OfWord_xmssClimb` adapter exposes the exact
  `hash16OfWord (xmssClimb ...)` byte root returned by a successful concrete XMSS
  spec call, `xmssClimb_roundtrip_of_node_roundtrip` and
  `xmssClimb_roundtrip_of_wots_success` prove the climb word's byte/word
  roundtrip from canonical nodes and successful WOTS starts, and
  `stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb` packages the exact
  post-step `"merkleNode"` equality from the model climb word plus that
  roundtrip; the `_wots_success` variant discharges that roundtrip directly
  from the concrete WOTS success fact, and the normalized variant isolates the
  remaining raw-cell normalization obligation; the normalized-cell adapter
  packages the exact `wordNormalize merkleNode = wordOfHash16 root` shape
  produced by the current frame theorem;
  `layerGuardsPass_of_c13HypertreeSpecStep_success`
  and `layerStep_of_c13HypertreeSpecStep_success` project those same concrete
  success facts into the guard trace and per-step relation consumed by the
  accept-path layer loop; their `_range` variants replace the impossible
  all-`Nat` layer surface with the actual `idx < 2` loop range, backed by
  `ClimbLoopGuarded.allGuardsPass_of_rel_range` and
  `CurrentNodeFrame.afterLayer_currentNode_wordOfHash16_of_forsPk_step_range`;
  `layerGuardsPass_of_c13HypertreeSpecStep_digitSum_success_range` exposes the
  guard side as the post-prefix `afterDigit ... "digitSum" = 208` model cell;
  `accept_path_returns_verifyParsed_bool_from_layer_step_range` exposes the same
  bounded step shape at the final accept handoff;
- pure C13 hypertree spec-fold closure in
  `SphincsMinusVerifiers/SegmentAcceptSpec.lean`:
  `specFold_c13HypertreeSpecStep_eq_of_foldHypertree_ok`, which derives the
  two-layer `ClimbLoop.specFold` result from successful concrete
  `foldHypertree`;
- canonical final word-comparison adapters in
  `SphincsMinusVerifiers/SegmentAcceptSpec.lean`:
  `hash16OfWord_beq_eq_decide`,
  `byteRoot_beq_eq_decide_of_wordOfHash16_roundtrip`,
  `wordCmp_of_wordOfHash16_roundtrip`,
  `hash16OfWord_wordOfHash16_hash16OfWord`,
  `base256_digit_decomp`,
  `base256_uint8_fold_init`,
  `base256_uint8_fold_lt`,
  `base256_fold_digit_of_list`,
  `baToNatBE_eq_data_toList`,
  `baToNatBE_lt_of_size`,
  `baToNatBE_hash16OfWord`,
  `wordOfHash16_hash16OfWord_highHalf`,
  `wordOfHash16_hash16OfWord_maskN_of_lt`,
  `forsPkWordC13_roundtrip`,
  `hash16OfWord_wordOfHash16_of_canonical`,
  `hash16OfWord_wordOfHash16_of_size`, and
  `specRoot_roundtrip_of_c13_fors_fold`;
- guarded layer-loop relation adapter
  `ClimbLoopGuarded.allGuardsPass_of_rel`;
- reject-subdomain correspondence over the accept-path `mkC13State` constructor
  and concrete `c13Primitives` in `SphincsMinusVerifiers/SegmentRejectSpec.lean`:
  `mkC13State_lookup_sigLength`, `c13_body_reverts_on_bad_length`,
  `c13_verifyBytes_none_on_bad_length`, and `c13_revert_on_bad_length` (bad
  signature length, fully discharged both sides), plus
  `c13_body_reverts_on_forced_zero` (FORS forced-zero guard, model side fully
  discharged), `c13_revert_on_forced_zero` (the older low-level form where the
  spec side is supplied as a surfaced `hCorr` hypothesis), and the parse-shaped
  `c13_verifyBytes_none_on_forced_zero_of_parse`,
  `c13_forcedZero_false_of_parse_s3Guard`, and
  `c13_revert_on_forced_zero_of_parse`, which discharge the C13 spec-side
  forced-zero reject result from successful concrete parsing plus the non-zero
  model guard.

The current narrow C13 accept handoff still has real residual obligations:

- range-gated FORS leaf-step seed-cell preservation, now reduced further by
  S4 setup/final-store frame facts and a statement-level outer-loop handoff.
  The final dynamic store offset is now proved to evaluate to `0x80 + 32*i`
  and not alias `0x00` for `i < 6`; `SegmentS4ForsMerkleFrame` connects the
  inner Merkle climb statement, whole leaf step, and full outer FORS loop to
  bounded or range-gated per-`stepMerkle` seed-cell preservation, so the
  remaining inner work is narrowed to supplying the setup bindings/bounds needed
  by `s4_eval_site_of_fors_frozen_calldata`, which now packages the FORS
  auth-path offset arithmetic, frozen-calldata masked sibling read, and
  `s4_address_assembly_eval_exists` address witness consumed by
  `stepMerkle_preserves_seed_slot_of_fors_frozen_calldata`; that frozen-calldata
  wrapper is now lifted through one leaf iteration and the full outer loop by
  `forsLeafStep_preserves_seed_slot_range_of_fors_frozen_calldata` and
  `execForsOuter_preserves_seed_slot_range_of_fors_frozen_calldata`.  The
  `SegmentS4ForsMerkleFrame.forsLeafSetupStep_fors_frozen_calldata_site`
  adapter packages the local straight-line setup facts into the frozen-calldata
  site shape, covering post-setup
  `authPtr = sigDataOffset + (128 + 304*i)`, bounded `pathIdx`, and a bounded
  existential `treeAdrsBase` witness for any incoming leaf state with the C13
  `"i"`/`"sigBase"` bindings.  The range-gated
  `forsTreeAdrsBase_eval_eq` / `forsLeafSetupStep_treeAdrsBase_eq_of_i`
  pair also identifies that setup binding exactly as
  `(3 <<< 96) ||| (i <<< 64)` for the six real FORS indices.  The separate
  `SegmentS4ForsMerkleFrame.forsLeafSetupStep_initial_forsClimbRel_of_eval`
  adapter packages `pathIdx = treeIdx` together with the setup `"node"` equality
  to the concrete spec FORS leaf hash word as the initial `MerkleClimbRel`;
  `forsLeafSetupStep_initial_forsClimbFrame_of_eval_site` combines that relation
  with the frozen-site selector/calldata, seed-cell, `treeAdrsBase`, and
  `authPtr` fields for the frame-carrying climb invariant.
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimb_of_eval`
  then lifts that initial relation through the 19-step inner fold to the named
  C13 `forsClimb` root, conditional on the existing per-height
  `MerkleClimbData` and relation-step obligations.
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site`
  is the matching frame-carrying handoff: it uses the exact setup
  `treeAdrsBase` theorem plus `MerkleClimbFrame_h_inject`, then calls
  `ClimbMemFrameMerkle.forsClimbFrame_model_node` under per-height frame-step
  obligations.
  Its `*_range` and `*_range_path_bound` siblings move the `idx < 19` and
  moving `pathIdx < 2^256` facts into the loop invariant, and
  `forsLeafInnerStep_node_eq_forsClimbFrame_of_fors_frozen_calldata` closes the
  frame-step side from the concrete C13 FORS auth-path calldata layout.
  `SegmentS4ForsMerkleFrame.stepMerkle_forsFrame_hstep_of_s4_data` now packages
  one such local frame step from the S4 `h1`/`h3` eval facts, calldata word
  load, bounds, and `MerkleClimbData`, reusing
  `ClimbMemFrameMerkle.MerkleClimbFrame_hstep`.
  `SegmentS4ForsMerkleFrame.stepMerkle_forsFrame_hstep_of_fors_frozen_calldata`
  specializes that package to the C13 FORS auth-path calldata layout, discharging
  the masked sibling load, concrete calldata-word equality, and address assembly
  from the frozen frame.
  `ClimbMemFrameMerkle.fors_climb_data_range_getD` supplies the matching
  `getD`-shaped `MerkleClimbData` range from the C13 parser auth-path projection
  and frozen-calldata word reads.
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsAllRootsC13_getElem_of_eval`
  rewrites that result to the exact `forsAllRootsC13[j]` normal-root getElem
  shape consumed by the six normal root-cell adapters.
  `ForsFrozenSite` and
  `stepMerkle_preserves_forsFrozenSite` now isolate the one-step invariant that
  carries those facts across a concrete inner Merkle step.  The pure
  `foldLoop_preserves_forsFrozenSite_range` and
  `foldLoop_preserves_seed_slot_of_forsFrozenSite_range` lemmas lift the site and
  seed-cell frames through the inner fold; the remaining work is connecting that
  fold-level package back to statement execution and the outer loop without the
  older arbitrary-state `hsite` premises.  The companion
  `foldLoop_preserves_root_cell_of_forsFrozenSite_range` gives the same pure
  fold-level preservation for ordinary root slots `0x80 + 32*j`.
  `forsLeafInnerStep_preserves_seed_slot_of_forsFrozenSite` and
  `forsLeafInnerStep_preserves_root_cell_of_forsFrozenSite` specialize the pure
  fold facts to the exact inner transformer, while
  `forsLeafStep_preserves_seed_slot_of_forsFrozenSetup` and
  `forsLeafStep_preserves_root_cell_ne_of_forsFrozenSetup` compose setup, inner,
  and final-store frames for one concrete leaf without arbitrary-state site
  premises;
- six named normal FORS root cells; `CurrentNodeFrame.normalRootCell_eq_of_outer_iteration_node`
  and `normalRootCells_eq_forsAllRootsC13_of_iteration_nodes` now package the
  outer-loop carry plus finalize pre-copy preservation into the exact accept-path
  `hmRlo` shape, leaving the per-iteration post-inner `"node"` equality against
  `forsAllRootsC13[j]` as the real data obligation.  The
  `normalRootCell_eq_of_fors_frozen_calldata_node` and
  `normalRootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes` adapters
  additionally discharge the later-iteration root-cell frame from the C13
  frozen-calldata/auth-path setup package, leaving the threaded setup facts and
  node/spec-root correspondence as the normal-root obligations.  The concrete
  `normalRootCell_eq_of_mkC13State_iteration_node` and
  `normalRootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes` adapters
  now discharge the six ordinary root memory-cell producers from the actual
  `mkC13State` outer-loop prefixes; they leave only the six post-inner `"node"`
  equalities against `forsAllRootsC13[j]`.
  `CurrentNodeFrame.forsOuterLeafState_node_eq_forsAllRootsC13_of_eval_parse`
  discharges the concrete seed slot and parsed auth-path `MerkleClimbData` range
  for one such post-inner equality.  Its `hMsg` specializations also discharge
  the concrete address bound, leaf-address setup eval, actual tree-index setup
  eval from the carried S2/S3 `"dVal"` digest, and parsed secret-key calldata
  eval from the actual outer-loop `"i"` binding and frozen C13 calldata image,
  leaving relation-step preservation as the remaining normal-root obligation.
  `CurrentNodeFrame.
  forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_tree_secret_parse_concrete`
  discharges that callback with the concrete frozen FORS auth-path calldata
  frame.  The forced-root root-cell
  value is reduced to the local scratch hash, parser SK projection, and
  final-secret calldata read by
  `CurrentNodeFrame.forcedRootCell_eq_forsAllRootsC13_of_parse_static`; the
	  static `afterFors` frame side is closed by
	  `afterFors_sigBase_mkC13State`, `afterFors_selector_mkC13State`, and
	  `afterFors_calldata_mkC13State`, while
	  `afterFors_seed_slot_mkC13State` and
	  `forcedRootCell_eq_forsAllRootsC13_of_parse_concrete` discharge the forced
	  root from the actual six C13 outer-loop prefixes.
	  `rootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes_and_parse_range_seed`
	  packages the six normal roots and forced root together as the final
	  `hmRlo`/`hmRlast` pair for the older range-seed path; the direct
	  `rootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes_and_parse`
	  variant removes that seed-frame premise, and
	  `rootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes_and_parse`
	  removes the frozen-site/root-cell producer premise for the concrete
	  frozen entry.  `rootCells_eq_forsAllRootsC13_of_hMsg_parse_concrete`
	  fixes the digest to the parsed C13 `H_msg` and discharges all seven root
	  cells directly from concrete parsing and the actual C13 outer leaf states.
	  `SegmentAcceptSpec.seed_named_pk_root_size_obligations_of_site_root_obligations`
	  now consumes that concrete wrapper directly for `hmRlo`/`hmRlast`.
	  `SegmentAcceptSpec.seed_named_leaf_obligations_of_leaf_root_obligations`
	  and
	  `accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_root_obligations_of_bytes`
	  plug that combined pair into the byte-shaped guarded accept handoff.
	  `seed_named_pk_root_size_obligations_of_site_root_obligations` and
	  `accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_site_root_obligations_of_bytes`
	  plug the direct concrete seed/root-cell bundle into the byte-shaped accept
	  handoff without constructing an intermediate `hLeaf`.  The concrete-layer adapter
	  `site_root_obligations_of_concrete_layer_site_root_obligations` and
	  `accept_path_returns_verifyParsed_bool_from_concrete_layer_site_root_obligations_of_bytes`
	  also fix `specStep` to `c13HypertreeSpecStep`, deriving `LayerGuardedStep`
	  and `hSpecFold` from concrete layer guard/success facts and `hFold`;
	  `seed_named_pk_root_size_obligations_of_concrete_layer_obligations`
	  and
	  `accept_path_returns_verifyParsed_bool_from_concrete_layer_obligations_of_bytes`
	  are the slimmer concrete-layer handoff that no longer asks callers for
	  FORS site facts or post-inner normal-root node correspondences.  The current
	  older concrete-layer obligation records quantify layer success over every
	  natural index, while `parseSignatureC13` produces exactly two layers; the
	  `no_concrete_layer_*_of_parse` counterexamples show why callers must use
	  `C13SeedNamedAcceptConcreteLayerRangeObligations`, whose accept theorem
	  consumes the range-gated guard/step/afterLayer adapters and asks for concrete
	  layer data-cell facts only for `idx < 2`;
- concrete C13 FORS outer-loop prefix setup facts in
  `CurrentNodeFrame.forsOuterPrefixState`,
  `CurrentNodeFrame.forsOuterLeafState`,
  `CurrentNodeFrame.forsOuterPrefix_sigBase_mkC13State`,
  `CurrentNodeFrame.forsOuterPrefix_selector_calldata_mkC13State`, and
  `CurrentNodeFrame.forsOuterPrefix_leafSetupFacts_mkC13State`, with named-state
  projections `CurrentNodeFrame.forsOuterLeafState_setupFacts_mkC13State`,
  `CurrentNodeFrame.forsLeafStep_preserves_seed_slot_of_mkC13State_prefix`,
  `CurrentNodeFrame.forsOuterPrefix_seed_slot_mkC13State`, and
  `CurrentNodeFrame.afterFors_seed_slot_mkC13State`:
  these package the actual prefix states visited by the six-iteration FORS outer
  loop with the rebound `"i"` value, S3 `"sigBase"`, selector, and frozen
  calldata image, then apply the concrete FORS setup theorem to prove the next
  leaf step preserves the seed slot for those real prefix states and lift that
  through all six concrete prefixes to `afterFors`.  The same concrete-prefix
  pattern now proves `forsLeafStep_preserves_root_cell_ne_of_mkC13State_prefix`,
  `forsOuterPrefix_root_cell_succ_ne_mkC13State`,
  `forsOuterPrefix_root_cell_suffix_mkC13State`, and
  `forsOuterPrefix_root_cell_iteration_node_mkC13State`, closing the ordinary
  root memory-cell producer side for real concrete states.  The remaining
  ordinary-root work is the post-inner node/spec-root correspondence;
- the local store half of each ordinary FORS root cell is isolated by
  `SegmentS4Fors.forsLeafStore_root_cell_range` and
  `SegmentS4Fors.forsLeafStep_root_cell_range`: one leaf iteration writes the
  post-inner-climb `"node"` value to `0x80 + 32*i`.  The local carry/non-alias
  side is now split out by
  `SegmentS4Fors.forsLeafStore_preserves_root_cell_range_ne`,
  `SegmentS4Fors.forsLeafStep_preserves_root_cell_range_ne_of_inner`, and the
  S4/Merkle bridge
  `SegmentS4ForsMerkleFrame.forsLeafStep_preserves_root_cell_range_ne_of_inner_step`;
  `ClimbLoop.foldLoop_memory_val_eq_step_at_of_suffix_preserves` and
  `SegmentS4Fors.forsOuter_root_cell_eq_iteration_node_of_suffix_preserves`
  close the outer-loop carry plumbing once later iterations are shown to
  preserve the selected root slot.  `stepMerkle_preserves_root_cell_of_s4_eval`,
  `stepMerkle_preserves_root_cell_of_fors_frozen_calldata`,
  `forsLeafStep_preserves_root_cell_range_ne_of_s4_eval`, and
  `forsOuter_root_cell_eq_iteration_node_of_s4_eval` reduce that suffix
  preservation side to the same C13 FORS frozen-calldata setup/bound facts used
  by the seed path, with
  `forsLeafStep_preserves_root_cell_range_ne_of_fors_frozen_calldata` and
  `forsOuter_root_cell_eq_iteration_node_of_fors_frozen_calldata` lifting the
  frozen-calldata package through one leaf iteration and the outer carry, and
  `CurrentNodeFrame.normalRootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes`
  now plugs that carry into the finalize pre-copy `hmRlo` shape.  For the
  concrete frozen entry, `normalRootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes`
  and `rootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes_and_parse`
  bypass the broad frozen-site premise entirely.  The remaining normal-root work
  is proving the per-height Merkle step preservation used to identify each
  post-inner node with `forsAllRootsC13[i]`.  The spec-side
  climb bridge for that work is now named by
  `ClimbStepSpec.forsTreeBase_node_address`,
  `ClimbStepSpec.forsClimb_eq_xmssClimb`, and the model-side wrappers
  `ClimbMemFrameMerkle.forsClimb_model_node` /
  `ClimbMemFrameMerkle.forsClimbFrame_model_node`; the S4 adapter
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimb_of_eval`
  applies that bridge to the concrete setup/inner-step shape, so FORS
  inner-climb callers can target the named C13 `forsClimb` root expression after
  discharging the per-height data obligations.  The setup-side
  `SegmentS4ForsMerkleFrame.forsLeafSetupStep_initial_forsClimbFrame_of_eval_site`
  now packages the initial frame fields for callers using the frame-carrying
  variant, and
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimbFrame_of_eval_site`
  consumes that package after rewriting `treeAdrsBase` to the exact C13 base.
  The companion
  `SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsAllRootsC13_getElem_of_eval`
  exposes the exact `forsAllRootsC13[j]` form expected by the existing normal
  root-cell handoff.  `CurrentNodeFrame.
  forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_tree_secret_parse_concrete`
  specializes the outer-leaf adapter to the actual `mkC13State` calldata image
  and removes the remaining per-height relation-step callback.
  existing Merkle frame/data obligations;
- per-layer guarded WOTS/XMSS correspondence through the range-gated concrete
  layer boundary.  `C13SeedNamedAcceptConcreteLayerRangeObligations` and
  `accept_path_returns_verifyParsed_bool_from_concrete_layer_range_obligations_of_bytes`
  now index the concrete handoff only over the actual C13 hypertree loop range
  `idx < 2`; `C13SeedNamedAcceptConcreteLayerDigitSumRangeObligations` and
  `accept_path_returns_verifyParsed_bool_from_concrete_layer_digitSum_range_obligations_of_bytes`
  further replace the raw guard premise with the natural `afterDigit`
  `"digitSum" = 208` fact.
  `C13SeedNamedAcceptConcreteLayerDigitCellRangeObligations` and
  `accept_path_returns_verifyParsed_bool_from_concrete_layer_digit_cell_range_obligations_of_bytes`
  reduce that guard side to the executable digit cell matching the concrete
  `wotsDigitSum (wotsDigest ...)`; the target `208` follows from the existing
  grinding-success fact, and `C13Concrete.wotsDigitSum_lt_uint256` supplies the
  overflow bound for the corresponding executable accumulator.
  `SegmentLayer3.digitSumStep_digitSum_eq` supplies the single-step executable
  arithmetic for that cell, and `SegmentLayer3.foldLoop_digitSum_eq` lifts it
  through the pure `forEach "ii"` image.  `digitSumFold_zero_eq_wotsDigitSum`
  closes the pure recursive-fold side.  The `beforeWotsDigest` scratch-frame
  bridge now proves executable `"d" = wotsDigest ...` and the post-prefix
  `"digitSum" = wotsDigitSum (wotsDigest ...)` once memory `[0x00,0x80)` is
  identified with seed, WOTS_HASH ADRS, current node, and count; the seed slot is
  now preserved by `beforeWotsDigest_seed_slot_eq`.  The remaining digit-cell gap
  is therefore proving the ADRS/current-node/count scratch-frame cells from the
  parsed layer inputs, followed by concrete
  WOTS/XMSS success and exact `"merkleNode"` model-cell facts through the
  bounded boundary.  The older
  concrete-layer packages still quantify
  success over every `idx : Nat`;
  `no_concrete_layer_site_root_obligations_of_parse` and
  `no_concrete_layer_obligations_of_parse` prove those packages are
  uninhabited for successfully parsed C13 signatures at `idx = 2`;
- remaining concrete data-cell proof for the new C13 hypertree layer step,
  now that the layer-success boundary has a loop/range-indexed shape;
- public-key byte sizes such as `pkRoot.size = 16`, as ABI boundary premises
  rather than Lean byte-spec consequences.  `C13Concrete.publicKeyOk_c13` and
  `C13Concrete.parsePublicKey_c13` accept arbitrary `ByteArray` public-key
  parts, and the `*_does_not_imply_pkRoot_size` /
  `*_does_not_imply_pkSeed_size` theorems give formal empty-part
  counterexamples at both the predicate and parser boundaries.

The successful C13 FORS/WOTS/XMSS/hypertree outputs now have standalone 16-byte
shape lemmas and `CanonicalHash16` propagation lemmas.  The base-256 arithmetic
lemma `SegmentAcceptSpec.hash16OfWord_wordOfHash16_hash16OfWord` now proves the
numeric roundtrip
`hash16OfWord (wordOfHash16 (hash16OfWord w)) = hash16OfWord w`; combined with
the C13 canonical-output facts,
`SegmentAcceptSpec.specRoot_roundtrip_of_c13_fors_fold` derives the spec-root
roundtrip from successful FORS reconstruction and hypertree folding.  The
public-key-root roundtrip is now reduced by
`SegmentAcceptSpec.hash16OfWord_wordOfHash16_of_size` to the ordinary byte-size
premise `pkRoot.size = 16`.  That premise cannot be derived from either
`publicKeyOk_c13` or `parsePublicKey_c13` in the current byte spec; the formal
counterexamples are
`C13Concrete.publicKeyOk_c13_does_not_imply_pkRoot_size` and
`C13Concrete.parsePublicKey_c13_does_not_imply_pkRoot_size`.  Once these
final-root roundtrips are available,
`SegmentAcceptSpec.wordCmp_of_wordOfHash16_roundtrip` derives the `hWordCmp`
premise without a global `LawfulBEq ByteArray` assumption.

The raw C13 length guard can now be derived from successful concrete parsing via
`SegmentAcceptSpec.c13_sig_length_of_parseSignatureC13`.  The S3 forced-zero
guard can now be derived from successful concrete parsing plus successful C13
`forcedZeroOk` via `SegmentAcceptSpec.c13_s3Guard_of_parse_forcedZero`.  The
current narrowest parsed-obligation handoff is
`SegmentAcceptSpec.C13SeedNamedAcceptGuardedObligations`, which no longer asks
callers to supply `hlen`, `hg3`, a whole `hgL` trace, or the layer-start relation
separately.  The trace is derived from `LayerGuardedStep`, and the start relation
is derived from the named S4/FORS seed/root frame by
`SegmentAcceptSpec.layerStart_of_seed_named_fors_roots_roundtrip`.
The adapter
`SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_parse`
also derives the C13 signature-shape guard from successful parsing via
`C13Concrete.parseSignatureC13_shape`, so the current parse-based handoff does
not require a separate `hShape` premise.  The byte-shaped adapter
`SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_bytes`
specializes the public key to the two contract-facing byte arguments, so that
handoff also no longer requires a separate `hPk` premise.  The public-key parse
fact itself is captured by `C13Concrete.parsePublicKey_c13`.  The further
byte-shaped roundtrip adapter
`SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_roundtrip_obligations_of_bytes`
replaces the raw `hWordCmp` field with the two canonical final-root roundtrips
and derives the word comparison internally via
`SegmentAcceptSpec.wordCmp_of_wordOfHash16_roundtrip`.
The next byte-shaped adapter,
`SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_roundtrip_obligations_of_bytes`.
It derives the spec-root roundtrip from successful C13 FORS reconstruction and
hypertree folding via `SegmentAcceptSpec.specRoot_roundtrip_of_c13_fors_fold`,
so its residual final-comparison surface keeps only the public-key-root
roundtrip `hash16OfWord (wordOfHash16 pkRoot) = pkRoot`.
The narrowest byte-shaped adapter is now
`SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_obligations_of_bytes`.
It also derives the FORS public-key masked-word roundtrip via
`SegmentAcceptSpec.forsPkWordC13_roundtrip`, so callers no longer supply
`wordOfHash16 (hash16OfWord forsPkWordC13) = forsPkWordC13`.
The size-based variant
`SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_obligations_of_bytes`
derives the remaining public-key-root roundtrip from `pkRoot.size = 16` via
`SegmentAcceptSpec.hash16OfWord_wordOfHash16_of_size`.  The leaf-frame variant
`SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_obligations_of_bytes`
also derives the `afterFors` seed-cell fact from the range-gated FORS
`forsLeafStep` preservation premise via
`CurrentNodeFrame.afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves`;
this is now the narrowest byte-shaped handoff.  It does not derive the public-key
root size from C13 public-key parsing, since `C13Concrete.publicKeyOk_c13`
records that C13 imposes no such low-byte public-key canonicality check.

## Safety Checks

Required scans for each proof pass:

```bash
rg -n "^\s*(sorry|admit)\b|exec\s*:=\s*verifyBytes" \
  SphincsMinusVerifiers SphincsMinusVerifierSpec
```

Only the strategy prose line should match.

```bash
rg -n "^(opaque execC13|axiom c13_refines_byte_spec|def c13Primitives|theorem c13_refines_spec)\b" \
  SphincsMinusVerifiers/Proofs.lean
```

Until final integration, this should show concrete `c13Primitives`, opaque
`execC13`, and axiom `c13_refines_byte_spec`.
