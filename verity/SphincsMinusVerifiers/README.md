# SPHINCS- Verity Models

This folder is the verification workbench for the three verifier contracts in
`src/`:

- `SphincsC13Asm_VerityModel` models `SPHINCs-C13Asm.sol`.
- `SPHINCs_C12Asm_VerityModel` models `SPHINCs-C12Asm.sol`.
- `SLH_DSA_SHA2_128_24_VerityModel` models `SLH-DSA-SHA2-128-24verifier.sol`.

The specs are layered in `SphincsMinusVerifierSpec/Spec.lean`:

- `verifyParsed` is the algorithmic spec over a parsed public key and parsed
  signature.
- `ByteLevel.verifyBytes` is the contract-facing spec for `pkSeed`, `pkRoot`,
  `message`, and `sig` bytes.  It owns signature length checks, public-key
  canonicality, signature parsing, and malformed-input behavior.
- `Model.lean` is the Verity implementation model.  It owns memory layout,
  scratch offsets, loops, low-level calls, and raw-Yul revert boundaries.

`Proofs.lean` contains **no `sorry`**.  The per-verifier refinement theorems are
unconditional; their only model-specific assumptions are three explicitly named
bridge axioms.

- `byteVerifier_refines_spec` proves, for *any* observable semantics `exec`,
  that a byte-level refinement composes with `verifyBytes_eq_verifySpec` into an
  abstract-spec refinement.  This is fully proved (`#print axioms` → `propext`).
- `c13_refines_byte_spec`, `c12_refines_byte_spec`, and
  `slhDsaSha2_128_24_refines_byte_spec` are **named axioms**: each asserts that
  one compiled Verity model refines its byte-level spec.  They are the Lean-level
  form of the `proofStatus := .assumed` local obligations already attached to the
  models in `Model.lean`, and they sit in the trust surface alongside the repo's
  keccak collision-resistance axioms.
- `c13_refines_spec`, `c12_refines_spec`, and `slhDsaSha2_128_24_refines_spec`
  (and their `*_implements_spec` forms) then conclude the abstract-spec
  refinement for each compiled model unconditionally, by feeding the matching
  bridge axiom into `byteVerifier_refines_spec`.

The primitive packages are deliberately not universally quantified: C13, C12,
and SHA2 use different hash/address/signature parsing semantics, and a single
compiled verifier cannot refine every possible `Primitives` instance.

The proof chain is:

```text
Verity implementation model
  refines                       ← assumed: *_refines_byte_spec axioms (MODEL-EXEC-BRIDGE)
ByteLevel.verifyBytes
  refines by construction       ← proved: byteVerifier_refines_spec
verifyParsed
```

## Current Fidelity

`Model.lean` uses Verity's ABI-aware `Bytes` parameter locals:

- `sig_length` corresponds to Solidity assembly `sig.length`.
- `sig_data_offset` corresponds to Solidity assembly `sig.offset`.

The C13 model expands the main Hmsg, FORS+C, WOTS+C, and hypertree assembly
shape in the Verity EDSL.  It preserves the scratch-memory addresses, masks,
loop bounds, digest bit extraction, branchless Merkle swaps, and final
`mstore(0x00, valid); return(0x00, 0x20)` behavior.

The C12 model expands the plain FORS, FORS-root compression, WOTS+ checksum and
chains, WOTS public-key compression, and five XMSS layers.  It follows the
Solidity memory offsets and signature offsets directly.

The SHA2 model expands the Hmsg precompile calls, FORS, WOTS+, WOTS public-key
compression, and XMSS climb.  It is structurally line-by-line, but it still
depends on a Verity-level SHA-256 precompile postcondition before the proof can
connect `mload` of the output buffer to the digest written by precompile `0x02`.

## Blockers

- `SHA2-PRECOMPILE`: the SHA2 verifier relies on repeated `staticcall(gas(),
  0x02, ...)`.  Verity can emit precompile calls, but the proof needs a stable
  postcondition tying output memory to SHA-256 over the exact input slice.
- `SHA2-PACKED-MEMORY`: the SHA2 verifier writes 16-byte values at unaligned
  offsets such as `0x56` and `0x66`.  The model can express this, but proofs need
  byte-slice memory lemmas, not just word-oriented `mstore` reasoning.
- `RAW-YUL-FIDELITY`: addressed on the companion Verity branch by adding typed
  `Stmt.unsafeYul` / `RawYul` fragments.  The models use this for Solidity
  `revert(0,0)` and for the hand-written `Error(string)` length/public-key
  checks, with local obligations attached at each raw-Yul boundary.  Remaining
  revert work is proving exact observable revert-data equivalence in Verity's
  executable semantics.
- `INLINE-YUL-FRONTEND`: this repository needs either direct inline-Yul syntax
  in Verity or an importer from Solidity/Yul into `CompilationModel.Stmt` /
  `Compiler.Yul.YulStmt`.  Hand translation is now present for all three linked
  verifiers, but it remains too error-prone for long-term maintenance.
- `MODEL-EXEC-BRIDGE`: the model-to-byte refinement is currently the named axiom
  `*_refines_byte_spec` for each verifier.  Replacing the axiom with a proof
  requires Verity's compiled-contract executable semantics over the
  `bytes`-calldata surface.  The current `Compiler/.../SourceSemantics.lean`
  interpreter (`interpretFunction` / `sourceContractSemantics`) evaluates decoded
  `Nat` arguments and does not yet model the raw `sig.length` / `sig.offset`
  calldata locals these verifiers read, so a faithful concrete `exec` cannot be
  supplied yet.  Once it can, define each `exec...` as that semantics and prove
  the corresponding `*_refines_byte_spec` (turning the axiom into a theorem); the
  `*_refines_spec` results then stay valid unchanged via
  `byteVerifier_refines_spec`.

## Build

```bash
cd verity
lake build SphincsMinusVerifiers
```

Expected status right now: build succeeds with **no `sorry` warnings**.
`Proofs.lean` proves `byteVerifier_refines_spec` outright and derives the
unconditional per-verifier `*_refines_spec` theorems from the three named
`*_refines_byte_spec` bridge axioms (MODEL-EXEC-BRIDGE).
