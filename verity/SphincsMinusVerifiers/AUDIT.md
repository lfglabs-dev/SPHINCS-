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

- Safe `execC13` integration shape: satisfied for the current partial branch.
  Evidence: `SphincsMinusVerifiers/ProofCore.lean` keeps exported `execC13`
  opaque while the concrete source-semantics runner is named
  `execC13Concrete`.  The reducer lemmas target `execC13Concrete`; final C13
  closure must replace `c13_refines_byte_spec` atomically with exposing the
  concrete runner at the exported boundary.

- `c13_refines_byte_spec` is a theorem, not an axiom: not satisfied.
  Evidence: `SphincsMinusVerifiers/Proofs.lean` still has
  `axiom c13_refines_byte_spec`.

- `#print axioms c13_refines_spec` has no bridge axiom: not satisfied yet.
  Current expected evidence still includes the bridge axiom because
  `c13_refines_byte_spec` remains an axiom.

- `lake build SphincsMinusVerifiers.Proofs` is green: satisfied for the current partial
  proof state.
  Last checked in this worktree on 2026-06-02 after restoring the opaque
  exported-`execC13`/internal-`execC13Concrete` split.

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

The current C13 work is still pre-integration.  Most bridge bricks are
standalone and do not use the bridge axiom.  The exported runner surface is in
the intended safe shape: `ProofCore.lean` keeps exported `execC13` opaque while
`execC13Concrete` carries the concrete source-semantics runner used by the
bridge-prep reducers.

Standalone bricks include:

- named FORS root/spec mirror facts in
  `SphincsMinusVerifierSpec/C13Concrete.lean`;
- C13 parse/forced-zero spec facts in
  `SphincsMinusVerifierSpec/C13Concrete.lean`:
  `parseSignatureC13_R`, `parseSignatureC13_shape`,
  `publicKeyOk_c13`, `parsePublicKey_c13`,
  `forcedZeroOk_c13_forsIndex_six`, and `hMsgC13_forsIndex_six`;
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
- S3 guard arithmetic facts in `SphincsMinusVerifiers/SegmentS3.lean`:
  `nat_land_low19` and `s3Guard_eq_forsIndex6`;
- Layer-3 pre-digest scratch-cell facts in
  `SphincsMinusVerifiers/SegmentLayer3.lean`:
  `beforeDigest_preserves_memory_zero` and
  `beforeDigest_memory_0x40_eq_currentNode`;
- seed and FORS-compression frame adapters in
  `SphincsMinusVerifiers/CurrentNodeFrame.lean`;
- generic memory-cell frame lemmas in
  `SphincsMinusVerifiers/MemoryFrame.lean`, including the per-statement,
  statement-list, raw `execForEachLoop`, and statement-level `.forEach`
  preservation lifts, plus bounded and range-gated raw `execForEachLoop` and
  statement-level `.forEach` memory-frame variants;
- Merkle-climb memory-frame adapters in
  `SphincsMinusVerifiers/ClimbMemFrameMerkle.lean`, including
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
  `stepMerkle_preserves_seed_slot_of_s4_eval`,
  `forsLeafInner_preserves_seed_slot_bound_of_s4_eval`,
  `s4_address_assembly_eval_exists`,
  `forsLeafInner_preserves_seed_slot_bound_of_step`,
  `forsLeafInner_preserves_seed_slot_range_of_step`,
  `forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound`, and
  `forsLeafStep_preserves_seed_slot_range_of_merkle_step_range`,
  `execForsOuter_preserves_seed_slot_range_of_merkle_step_bound`, and
  `execForsOuter_preserves_seed_slot_range_of_merkle_step_range`, and
  `execForsOuter_preserves_seed_slot_range_of_s4_eval`;
- S4 FORS body split plus setup/final-store frame facts in
  `SphincsMinusVerifiers/SegmentS4Fors.lean`:
  `forsLeafBody_eq_segments`, `execForsLeafSetup`,
  `forsLeafSetup_preserves_seed_slot`, `forsLeafSetup_preserves_i`,
  `forsLeafSetupStep_preserves_seed_slot`,
  `forsLeafSetupStep_preserves_i`, `execForsLeafInner`,
  `forsLeafInner_preserves_i`,
  `execForsLeafStore`, `forsLeafStore_preserves_seed_slot_of_offset`,
  `forsLeafStore_preserves_i`, `forsLeafBody_preserves_i`,
  `forsLeafStep_preserves_i`,
  `forsLeafBody_preserves_seed_slot_range_of_inner`,
  `forsLeafStep_preserves_seed_slot_range_of_inner`,
  `eval_forsLeafStore_offset`,
  `forsLeafStore_offset_ne_zero`, `forsLeafStore_preserves_seed_slot_range`,
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
  `C13SeedNamedAcceptGuardedPkRootSizeLeafObligations` contracts in
  `SphincsMinusVerifiers/SegmentAcceptSpec.lean`;
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
  `ClimbLoopGuarded.allGuardsPass_of_rel`.

The current narrow C13 accept handoff still has real residual obligations:

- range-gated FORS leaf-step seed-cell preservation, now reduced further by
  S4 setup/final-store frame facts and a statement-level outer-loop handoff.
  The final dynamic store offset is now proved to evaluate to `0x80 + 32*i`
  and not alias `0x00` for `i < 6`; `SegmentS4ForsMerkleFrame` connects the
  inner Merkle climb statement, whole leaf step, and full outer FORS loop to
  bounded or range-gated per-`stepMerkle` seed-cell preservation, so the
  remaining inner work is narrowed to the site-specific masked sibling calldata
  read plus the ordinary binding/bounds facts needed by
  `s4_address_assembly_eval_exists` to produce the address-assembly eval
  consumed by `stepMerkle_preserves_seed_slot_of_s4_eval` and lifted through the
  inner climb and full outer loop by the `*_of_s4_eval` adapters;
- six named normal FORS root cells plus the forced root cell;
- per-layer guarded WOTS/XMSS correspondence;
- hypertree layer-step and fold correspondence;
- executable checksum/current-node facts for the two concrete C13 hypertree
  layer states.

The successful C13 FORS/WOTS/XMSS/hypertree outputs now have standalone 16-byte
shape lemmas and `CanonicalHash16` propagation lemmas.  The base-256 arithmetic
lemma `SegmentAcceptSpec.hash16OfWord_wordOfHash16_hash16OfWord` now proves the
numeric roundtrip
`hash16OfWord (wordOfHash16 (hash16OfWord w)) = hash16OfWord w`; combined with
the C13 canonical-output facts,
`SegmentAcceptSpec.specRoot_roundtrip_of_c13_fors_fold` derives the spec-root
roundtrip from successful FORS reconstruction and hypertree folding.
`SegmentAcceptSpec.wordCmp_of_wordOfHash16_rootMatchesPk_c13` now derives the
`hWordCmp` premise against `rootMatchesPk c13`, the byte-spec low-16-byte
projection of the contract's full-word public-key root.  The old
`pkRoot.size = 16` public-root roundtrip premise is no longer part of the current
C13 word-comparison handoff.

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
The older size-based variant
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
