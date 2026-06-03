# Trust Assumptions

Status date: 2026-06-01

This document records what the C13/C12 MODEL-EXEC-BRIDGE proof is intended to
close, and what remains outside its scope.

## In Scope

- Model-to-byte verifier correspondence for C13 first, then C12 only after the
  C13 pattern is proved.

- Concrete C13 primitives routed through the same Keccak engine shape used by
  the interpreter-side memory hashing.

- Standalone segment, memory-frame, FORS, and accept-path lemmas that do not
  touch `execC13` or `c13_refines_byte_spec` before final integration.

- Standalone reject-subdomain lemmas (`SegmentRejectSpec`) framed over the
  accept-path `mkC13State` constructor and concrete `c13Primitives`.  The
  bad-length correspondence is fully discharged on both sides.  The FORS
  forced-zero revert is discharged on the model side.  The older low-level
  theorem `c13_revert_on_forced_zero` still accepts the spec-side result as an
  explicit `hCorr` hypothesis, but the parse-shaped C13 theorem
  `c13_revert_on_forced_zero_of_parse` now discharges that spec-side
  `verifyBytes = none` result from successful concrete parsing and the non-zero
  model guard.  These do not touch `execC13` or the bridge axiom and do not
  change the bridge trust surface.

- Boundary byte-shape premises, such as `pkRoot.size = 16`, may remain as
  explicit input-shape obligations until they are connected to a parser, ABI, or
  caller-side assumption.

- Local frame obligations, such as the range-gated FORS leaf-step
  seed-preservation fact, may remain explicit until their statement-level memory
  frame lemmas are connected to the final accept adapter.  The generic
  `MemoryFrame` kit, including its raw `execForEachLoop` and statement-level
  `.forEach` memory preservation lifts and its bounded/range-gated raw loop and
  statement-level variants, S4 FORS setup/final-store frame facts, the
  whole-leaf outer-index binding frame, the conditional whole-leaf seed-cell
  frame from an inner-climb seed premise, the Merkle-climb statement-level
  memory-frame adapters in `ClimbMemFrameMerkle` including bounded and
  range-gated variants, the `SegmentS4ForsMerkleFrame` adapters from the S4
  inner climb, whole leaf step, and full outer FORS loop to per-`stepMerkle`
  seed-frame premises, the local Merkle parity-packaged per-step seed-cell
  wrappers and S4-shaped specialization plus inner/full-loop lifts, together
  with the S4 address-assembly eval witness from ordinary binding/bounds facts,
  that leave only site-specific sibling read plus those binding/bounds inputs,
  the statement-level
  outer-loop seed-cell handoff in both `wordNormalize 6` and `idx < 6` forms,
  in-range final-store offset non-aliasing lemmas, the parser-side FORS secret
  word projection `C13Concrete.parseSignatureC13_fors_sk_getElem?`, and the
  local forced-root scratch-cell proof
  `SegmentS4Finalize.forsFinalizePreCopyStep_forced_root_cell`, plus the
  CurrentNodeFrame final-secret calldata and forced-root parsed-cell adapters,
  are in scope as standalone bridge bricks; they do not change the bridge trust
  surface.  The forced-root accept-boundary static frame is closed by
  `CurrentNodeFrame.afterFors_sigBase_mkC13State`,
  `afterFors_selector_mkC13State`, and `afterFors_calldata_mkC13State`; the
  packaged forced-root cell handoff is
  `forcedRootCell_eq_forsAllRootsC13_of_parse_range_seed`.

## Out Of Scope

- Source-to-model fidelity for the hand-written Solidity/Yul model.
  The proof closes the model-to-byte/spec bridge, not the claim that the model
  was mechanically imported from source.  Differential testing or a future
  frontend importer is separate work.

- SHA-2 verifiers.
  They remain blocked on byte-addressed memory modeling and are explicitly out
  of scope for `STRATEGY.md`.

- C12 bridge discharge before C13 is complete.
  The early model-shape word-alignment check for C12's 16-byte truncation
  behavior has passed: `c12VerifyBody` carries 16-byte values as masked words
  and stores them at word-aligned offsets, unlike the SHA-2 packed-memory model.
  This does not discharge C12; it only means the known SHA-2 byte-addressed
  memory blocker was not found in the C12 model.

## Soundness Rule

`execC13` must stay opaque while `c13_refines_byte_spec` is still an axiom.
The concrete interpreter definition of `execC13` and the theorem replacing
`c13_refines_byte_spec` must land in one atomic change.  This prevents converting
the current abstract bridge assumption into a closed claim about a concrete
interpreter before the proof exists.
