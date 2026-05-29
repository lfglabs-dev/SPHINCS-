# SPHINCS- Verity Models

This folder is the verification workbench for the three verifier contracts in
`src/`:

- `SphincsC13Asm_VerityModel` models `SPHINCs-C13Asm.sol`.
- `SPHINCs_C12Asm_VerityModel` models `SPHINCs-C12Asm.sol`.
- `SLH_DSA_SHA2_128_24_VerityModel` models `SLH-DSA-SHA2-128-24verifier.sol`.

The clean mathematical spec is in `SphincsMinusVerifierSpec/Spec.lean`.  The
proof hooks in `Proofs.lean` state that each model must implement the matching
spec; they intentionally use `sorry` until the executable semantics are wired
all the way through Verity.

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
- `MODEL-EXEC-BRIDGE`: `Proofs.lean` uses opaque `exec...` functions.  These
  must be replaced with Verity's compiled-contract executable semantics before
  the `ImplementsVerifier` theorems become meaningful refinement theorems.

## Build

```bash
cd verity
lake build SphincsMinusVerifiers
```

Expected status right now: build succeeds with three `sorry` warnings in
`Proofs.lean`.
