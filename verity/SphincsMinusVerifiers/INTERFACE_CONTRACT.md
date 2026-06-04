# C13 interface contract (boss-frozen segment map)

Derived from the actual `c13VerifyBody` (Model.lean:103-226) and `SPHINCs-C13Asm.sol`,
this CORRECTS the idealized S1-S6 table in STRATEGY.md §2 to match the real control
flow. Phase 2 workers code against THIS, not the strategy table.

## Top-level statement indices of `c13VerifyBody`

| idx | statement | segment |
|---|---|---|
| 0 | length-guard `ite` (revert if `sig_length ≠ 3688`) | **S1** (done: reject/pass lemmas) |
| 1 | canonical public-key guard (revert if `pkSeed/root != pkSeed/root & N_MASK`) | S1b |
| 2-4 | `seed`,`root` lets; `mstore 0x00 seed` | S2 setup |
| 5-9 | `R` let; `mstore 0x20/0x40/0x60/0x80` (Hmsg preimage) | S2 setup |
| 10 | `digest = keccak 0x00 0xA0` | **S2** (first-keccak lemma done) |
| 11-17 | `htIdx`, `dVal`, forced-zero `ite` normal-`false` return, `sigBase`, `idxLeaf0`, `idxTree0`, `forsBase` | **S3** index extraction + FORS base |
| 18 | `forEach i<6` FORS normal trees (NESTED `forEach h<19` Merkle climb) | **S4a** (LOOP, not straight-line) |
| 19-22 | last (forced-zero) FORS tree leaf hash → `mstore 0x140` | S4b |
| 23-24 | `mstore 0x20` FORS_ROOTS adrs; `forEach i<7` copy roots to scratch | S4c |
| 25 | `forsPk = keccak 0x120` | **S4** result = `forsRootBytes` |
| 26-28 | `currentNode=forsPk`, `idxTree=htIdx`, `sigOff=1952` | climb setup |
| 29 | `forEach layer<2` hypertree climb | **Layer 3** |
| 30 | `valid = eq currentNode root` | final compare |
| ++ | `returnBoolFromWord "valid"` | return |

## Corrections vs STRATEGY table
- **S4 is a double loop**, not straight-line: outer `i<6` over FORS trees, each with an
  inner `h<19` branchless-Merkle auth-path climb, then a forced-zero 7th tree, then a
  7-root compression keccak. Needs a loop-invariant proof, not `cons_continue` chaining.
- **S5/S6 do not exist as a prefix.** There is no pre-loop "WOTS on FORS root → first HT
  leaf". The FORS root seeds `currentNode` directly; ALL WOTS+XMSS work happens INSIDE
  the `layer<2` loop. So STRATEGY's S5 (WOTS pk) and S6 (HT leaf) are subsumed into
  iteration 0 of the Layer-3 loop.
- **Current upstream C13 returns `false`, not `revert(0,0)`, for forced-zero and
  WOTS checksum misses.** Length and non-canonical public-key failures still
  revert with `Error(string)`.
- **FORS addresses are keyed by the bottom hypertree leaf.** S3 now computes
  `idxLeaf0`, `idxTree0`, and `forsBase`; S4 leaf/node/root-compression addresses
  all include these fields.

## Reusable shapes (Layer-1 kit targets)
Three structurally identical **branchless-Merkle-climb** loops appear:
- FORS auth path: `forEach h<19` (Model.lean:139-150)
- XMSS auth path: `forEach h<11` (Model.lean:207-216)
Both use `s := shl 5 (and idx 1)`; `mstore (xor 0x40 s) node`; `mstore (xor 0x60 s) sib`;
`node := and (keccak 0x00 0x80) N_MASK`; `idx := idx>>1`. ONE parametric lemma
`merkleClimbStep` covers both — no path case-split (branchless swap is the whole point).

One **WOTS chain** shape: `forEach step<steps` (Model.lean:174-178) repeatedly hashes
`val := and (keccak 0x00 0x60) N_MASK` under `chainBase | (digit+step)`. One lemma covers it;
the outer `i<43` then folds 43 independent chains into scratch.

## Pre_i / Post_i contract (symbolic memory as assoc list)
Each segment lemma has the shape:
> Given `RuntimeState s` whose symbolic memory satisfies `Pre_i` and whose bindings
> contain the named inputs, `execStmtList [] s segment_i = .continue s'`, where `s'`'s
> symbolic memory satisfies `Post_i` and the produced/bound value equals
> `<spec intermediate>_i` (computed via `c13Primitives`).

Memory is tracked as a finite `(addr, value)` association list; later reads resolve by
lookup (`mload_mstore_same`/`_diff`), never by replaying history. Word addresses in play:
`0x00,0x20,0x40,0x60,0x80,0xA0` (scratch) and `0x80 + 32*i` for i∈[0,6] (FORS root slots,
top at `0x140`), plus `0x40 + 32*i` compression slots.

## Spec mirror intermediates (Worker D must expose, matching boundaries above)
`digestBytes` (S2) · `htIndex`/`forsIndices` (S3) · `forsRootBytes` (S4) ·
per-layer `wotsPkBytes`/`xmssRootBytes` and `htClimb layer node` (Layer 3) ·
`finalRootBytes`. Prove `verifyBytes c13Primitives c13Variant = compose-of-these` once.

## Gate dependency
ALL of the above is unprovable until Phase 0 concretizes `c13Primitives` so the spec's
hash equals the interpreter's `KeccakEngine.keccak256` over the same byte preimage. Do
not start Phase 2 until the gate worker reports PASS.
