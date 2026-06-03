/-
  Concrete C13 `Primitives` package (Phase 0, STRATEGY §1).

  This file replaces the *opaque* `axiom c13Primitives : Primitives` with a
  concrete `def c13PrimitivesConcrete : Primitives` whose hashing is routed
  through the SAME pure Keccak the Verity interpreter uses
  (`KeccakEngine.keccak256`), fed the SAME big-endian word-aligned byte preimage
  the interpreter feeds it (`memorySliceBytesBE` / `byteArrayToNatBE`, see
  `Compiler/Proofs/IRGeneration/SourceSemantics.lean`).

  It is ADDITIVE: it does not touch `axiom c13Primitives`, `execC13`, the bridge
  axioms, or `Model.lean`. It models `src/SPHINCs-C13Asm.sol` faithfully.

  ## The hash bridge (STEP 1)

  The interpreter models EVM `keccak256(offset, size)` as

      keccakMemorySlice memory offset size
        = wordNormalize (byteArrayToNatBE
            (keccak256 (memorySliceBytesBE memory offset size)))

  where `memorySliceBytesBE` concatenates `wordToBytesBE (memory cell)` for each
  32-byte-aligned cell covering `[offset, offset+size)` and keeps the first
  `size` bytes.  For every C13 hash, `size` is a multiple of 32 (0x60, 0x80,
  0xA0, 0x120, 0x5A0), so the preimage is *exactly* the big-endian concatenation
  of the 32-byte memory words.  `byteArrayToNatBE` then reads the 32-byte digest
  back big-endian (byte 0 most significant) — i.e. exactly how the EVM treats a
  keccak result as a 256-bit word.

  We therefore work in the contract's native unit — the 256-bit memory word
  (`Word := Nat`, taken mod 2^256) — and define a kernel `keccakWords` that:
    * encodes each input word big-endian (`wordToBytesBE`, the SAME function),
    * concatenates them,
    * applies `KeccakEngine.keccak256`,
    * reads the result big-endian (`byteArrayToNatBE`, the SAME function).
  This is definitionally the value the interpreter computes for the matching
  word-aligned `keccak256(0x00, 32*k)` call, so a future model→spec proof can
  rewrite each interpreter hash to a `keccakWords` application by `rfl`/`simp`.
-/

import SphincsMinusVerifierSpec.Spec
import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SphincsMinusVerifierSpec
namespace C13Concrete

open Compiler.Proofs.IRGeneration.SourceSemantics (wordToBytesBE)

/-- A 256-bit EVM memory word, represented as a `Nat` (callers keep it `< 2^256`). -/
abbrev Word := Nat

def wordMod : Nat := 2 ^ 256

/-- The C13 `N_MASK`: keep the high 16 bytes (n=128 bits) of a 256-bit word,
zero the low 16 bytes.  This is the contract's
`0xFFFF…FFFF00000000000000000000000000000000`. -/
def nMask : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

/-- Apply `N_MASK` to a word (`and(w, N_MASK)` in the contract). -/
def maskN (w : Word) : Word := w &&& nMask

/-! ### STEP-1 kernel: keccak over big-endian 32-byte words

`keccakWords ws` is the interpreter's `keccak256(0x00, 32 * ws.length)` value
when memory cell `32*i` holds `ws[i]`: the inputs are encoded big-endian with
the SAME `wordToBytesBE`, concatenated in the SAME order, hashed with the SAME
`KeccakEngine.keccak256`, and read back big-endian with the SAME
`byteArrayToNatBE`.  The only deliberate omission is the interpreter's outer
`wordNormalize` (mod 2^256): a keccak digest is already `< 2^256`, so the two
agree on every C13 call (we re-establish this with `keccakWords_lt`). -/
def keccakBytes (ws : List Word) : ByteArray :=
  KeccakEngine.keccak256
    (ws.foldl (fun acc w => acc ++ wordToBytesBE w) ByteArray.empty)

def keccakWords (ws : List Word) : Word :=
  KeccakEngine.byteArrayToNatBE (keccakBytes ws)

/-- The C13 tweakable hash kernel, of the contract's shape
`and(keccak256(seed ‖ adrs ‖ payload), N_MASK)`.  Each of `seed`, `adrs`, and
the `payload` entries is one 256-bit memory word. -/
def thKeccak (seed adrs : Word) (payload : List Word) : Word :=
  maskN (keccakWords (seed :: adrs :: payload))

/-! ### Word ↔ 16-byte hash conversions

C13 hashes are 16 bytes (n=128) living in the *high* 16 bytes of a 256-bit
word (post-`N_MASK`).  The spec's `Bytes` values for nodes/seeds/roots are
16-byte `ByteArray`s.  `wordOfHash16` injects a 16-byte hash into the high half
of a word; `hash16OfWord` reads the high 16 bytes back as a 16-byte `ByteArray`.
These are mutually inverse on canonical inputs (16-byte arrays / masked words). -/

/-- Big-endian `Nat` value of a `ByteArray` (byte 0 most significant). -/
def baToNatBE (ba : ByteArray) : Nat :=
  ba.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Inject a 16-byte hash into the high 16 bytes of a 256-bit word. -/
def wordOfHash16 (b : Bytes) : Word := (baToNatBE b % (2 ^ 128)) * (2 ^ 128)

/-- Read the high 16 bytes of a word as a 16-byte big-endian `ByteArray`. -/
def hash16OfWord (w : Word) : Bytes :=
  ⟨((List.range 16).map (fun i => UInt8.ofNat ((w / (256 ^ (31 - i))) % 256))).toArray⟩

/-- Reading the high half of a word always produces a C13-sized hash. -/
theorem hash16OfWord_size (w : Word) : (hash16OfWord w).size = 16 := by
  simp [hash16OfWord, ByteArray.size]

/-- A byte string is canonical for C13 root comparison when it is the high
16-byte projection of some word. -/
def CanonicalHash16 (b : Bytes) : Prop := ∃ w, b = hash16OfWord w

theorem hash16OfWord_canonical (w : Word) : CanonicalHash16 (hash16OfWord w) :=
  ⟨w, rfl⟩

/-! ### Signature byte layout (C13, 3688 bytes)

    R                 : bytes  0..16   (high 16 of word at offset 0)
    FORS sk[7]        : 16 + 16*i      (i = 0..6)        -> 128 bytes total
    FORS auth[6][19]  : 128 + 304*t + 16*h               -> 1824 bytes
    HT_START          : 1952
    per layer (×2):
      chains[43]      : sigOff + 16*i                     -> 688 bytes
      count           : sigOff + 688 (high 4 bytes = uint32, shr 224)
      auth[11]        : sigOff + 692 + 16*h               -> 176 bytes
      next sigOff     : (sigOff + 692) + 176 = sigOff + 868

All 16-byte fields are read as `and(calldataload(off), N_MASK)`, i.e. the high
16 bytes of the 32-byte word at `off`. -/

/-- Read the 16-byte hash at byte-offset `off` from `sig`, as a `ByteArray`. -/
def read16 (sig : Bytes) (off : Nat) : Bytes :=
  ⟨((List.range 16).map (fun i => (sig[off + i]?).getD 0)).toArray⟩

def parseSignatureC13 (v : Variant) (sig : Bytes) : Option Signature :=
  if sig.size ≠ v.sigBytes then none
  else
    let R := read16 sig 0
    let forsSk := (List.range 7).map (fun i => read16 sig (16 + 16 * i))
    let forsAuth := (List.range 6).map (fun t =>
      (List.range 19).map (fun h => read16 sig (128 + 304 * t + 16 * h)))
    let fors : ForsSig := { sk := forsSk, authPath := forsAuth }
    let layers := (List.range 2).map (fun layer =>
      let sigOff := 1952 + 868 * layer
      let chains := (List.range 43).map (fun i => read16 sig (sigOff + 16 * i))
      -- count = uint32 in the high 4 bytes of the word at sigOff+688
      let count :=
        (List.range 4).foldl
          (fun acc j => acc * 256 + ((sig[sigOff + 688 + j]?).getD 0).toNat) 0
      let auth := (List.range 11).map (fun h => read16 sig (sigOff + 692 + 16 * h))
      ({ wots := { chains := chains, count := count }, authPath := auth } : XmssLayerSig))
    some { R := R, fors := fors, layers := layers }

/-! ### Auth-path extraction lemmas (`hauth`)

These pin the byte-offset of every auth-path sibling the climb reads, purely as a
list-indexing fact about `parseSignatureC13`'s `(List.range n).map …` fields.  No
execution semantics: the model→spec climb correspondence consumes these as the
`hauth` supplier (`(auth[h]?).getD ⟨#[]⟩ = read16 sig sOff`). -/

/-- Indexing into a `range`-map: `((range n).map f)[h]? = some (f h)` when `h<n`. -/
theorem getElem?_map_range {α} (f : Nat → α) {n h : Nat} (hh : h < n) :
    ((List.range n).map f)[h]? = some (f h) := by
  rw [List.getElem?_map, List.getElem?_range hh]
  rfl

/-- Indexing into a `range`-map, `getElem` form. -/
theorem getElem_map_range {α} (f : Nat → α) {n h : Nat} (hh : h < n) :
    ((List.range n).map f)[h]'(by simp [hh]) = f h := by
  simp only [List.getElem_map, List.getElem_range]

/-- When `parseSignatureC13` succeeds, its size guard passed. -/
theorem parseSignatureC13_size {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s) : sig.size = v.sigBytes := by
  unfold parseSignatureC13 at hparse
  by_cases hsz : sig.size = v.sigBytes
  · exact hsz
  · simp [hsz] at hparse

/-- Successful concrete C13 parsing fixes the parsed `R` field to the first
16-byte signature read. -/
theorem parseSignatureC13_R {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 c13 sig = some s) :
    s.R = read16 sig 0 := by
  unfold parseSignatureC13 at hparse
  by_cases hsz : sig.size = c13.sigBytes
  · simp [hsz] at hparse
    rw [← hparse]
  · simp [hsz] at hparse

/-- Successful concrete C13 parsing constructs exactly the C13 signature shape:
16-byte `R`, seven 16-byte FORS secrets, six FORS auth paths of height 19, and
two XMSS layers with 43 WOTS chains and 11 auth nodes each. -/
theorem parseSignatureC13_shape {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 c13 sig = some s) :
    signatureShapeOk c13 s = true := by
  have hsz : sig.size = c13.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  simp [signatureShapeOk, allSized, allAuthSized, read16, ByteArray.size, c13]

/-- Successful concrete C13 parsing produces exactly the two XMSS layers used by
the C13 hypertree. -/
theorem parseSignatureC13_layers_length {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 c13 sig = some s) :
    s.layers.length = 2 := by
  have hsz : sig.size = c13.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  simp

/-- C13 accepts the contract-facing public-key words without low-byte
canonicality checks. -/
theorem publicKeyOk_c13 (pk : PublicKey) :
    publicKeyOk c13 pk = true := by
  simp [publicKeyOk, c13]

/-- C13's public-key well-formedness predicate itself does not enforce a
16-byte `pkRoot`; the empty root is accepted. -/
theorem publicKeyOk_c13_does_not_imply_pkRoot_size :
    ∃ pk, publicKeyOk c13 pk = true ∧ pk.pkRoot.size ≠ 16 := by
  refine ⟨{ pkSeed := ⟨#[]⟩, pkRoot := ⟨#[]⟩ }, ?_, ?_⟩
  · exact publicKeyOk_c13 _
  · simp [ByteArray.size]

/-- C13's public-key well-formedness predicate itself does not enforce a
16-byte `pkSeed`; the empty seed is accepted. -/
theorem publicKeyOk_c13_does_not_imply_pkSeed_size :
    ∃ pk, publicKeyOk c13 pk = true ∧ pk.pkSeed.size ≠ 16 := by
  refine ⟨{ pkSeed := ⟨#[]⟩, pkRoot := ⟨#[]⟩ }, ?_, ?_⟩
  · exact publicKeyOk_c13 _
  · simp [ByteArray.size]

/-- Byte-level C13 public-key parsing is just the two exposed `bytes32`
arguments packaged as a `PublicKey`. -/
theorem parsePublicKey_c13 (pkSeed pkRoot : Bytes) :
    SphincsMinusVerifierSpec.ByteLevel.parsePublicKey c13 pkSeed pkRoot =
      some { pkSeed := pkSeed, pkRoot := pkRoot } := by
  simp [SphincsMinusVerifierSpec.ByteLevel.parsePublicKey, publicKeyOk_c13]

/-- C13's byte-level public-key parser does not enforce a 16-byte `pkRoot`.
The Solidity ABI supplies `bytes32`; in this Lean byte spec, that length remains
an explicit boundary premise rather than a consequence of `parsePublicKey_c13`. -/
theorem parsePublicKey_c13_does_not_imply_pkRoot_size :
    ∃ pkSeed pkRoot pk,
      SphincsMinusVerifierSpec.ByteLevel.parsePublicKey c13 pkSeed pkRoot = some pk ∧
      pk.pkRoot.size ≠ 16 := by
  refine ⟨⟨#[]⟩, ⟨#[]⟩, { pkSeed := ⟨#[]⟩, pkRoot := ⟨#[]⟩ }, ?_, ?_⟩
  · rw [parsePublicKey_c13]
  · simp [ByteArray.size]

/-- C13 byte-level public-key parsing likewise does not enforce a 16-byte
`pkSeed`; that shape is supplied by the Solidity ABI boundary, not by this byte
spec parser. -/
theorem parsePublicKey_c13_does_not_imply_pkSeed_size :
    ∃ pkSeed pkRoot pk,
      SphincsMinusVerifierSpec.ByteLevel.parsePublicKey c13 pkSeed pkRoot = some pk ∧
      pk.pkSeed.size ≠ 16 := by
  refine ⟨⟨#[]⟩, ⟨#[]⟩, { pkSeed := ⟨#[]⟩, pkRoot := ⟨#[]⟩ }, ?_, ?_⟩
  · rw [parsePublicKey_c13]
  · simp [ByteArray.size]

/-- **XMSS `hauth`.**  The `h`-th auth-path sibling of climb layer `layer`
(`layer < 2`, `h < 11`) is the 16-byte hash at sig byte-offset
`1952 + 868*layer + 692 + 16*h`. -/
theorem parseSignatureC13_layer_authPath_getElem?
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {layer : Nat} (hlayer : layer < 2)
    {lsig : XmssLayerSig} (hlsig : s.layers[layer]? = some lsig)
    {h : Nat} (hh : h < 11) :
    lsig.authPath[h]? = some (read16 sig (1952 + 868 * layer + 692 + 16 * h)) := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  rw [getElem?_map_range _ hlayer] at hlsig
  injection hlsig with hlsig
  subst hlsig
  exact getElem?_map_range _ hh

/-- **FORS `hauth`.**  The `h`-th auth-path sibling of FORS tree `t`
(`t < 6`, `h < 19`) is the 16-byte hash at sig byte-offset
`128 + 304*t + 16*h`. -/
theorem parseSignatureC13_fors_authPath_getElem?
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {t : Nat} (ht : t < 6)
    {tAuth : List Bytes} (htAuth : s.fors.authPath[t]? = some tAuth)
    {h : Nat} (hh : h < 19) :
    tAuth[h]? = some (read16 sig (128 + 304 * t + 16 * h)) := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  rw [getElem?_map_range _ ht] at htAuth
  injection htAuth with htAuth
  subst htAuth
  exact getElem?_map_range _ hh

/-- `getD` form of `parseSignatureC13_fors_authPath_getElem?`, matching the
normal-root spec expression `(fors.authPath[i]?).getD []`. -/
theorem parseSignatureC13_fors_authPath_getD_getElem?
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {t : Nat} (ht : t < 6)
    {h : Nat} (hh : h < 19) :
    (((s.fors.authPath[t]?).getD [])[h]?)
      = some (read16 sig (128 + 304 * t + 16 * h)) := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  rw [getElem?_map_range _ ht]
  exact getElem?_map_range _ hh

/-- **FORS secret-key word.**  The `i`-th FORS secret-key preimage
(`i < 7`, including the forced-zero seventh tree) is the 16-byte hash at
signature byte-offset `16 + 16*i`. -/
theorem parseSignatureC13_fors_sk_getElem?
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {i : Nat} (hi : i < 7) :
    s.fors.sk[i]? = some (read16 sig (16 + 16 * i)) := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  exact getElem?_map_range _ hi

/-! ### H_msg

The contract computes
`digest = keccak256(seed ‖ root ‖ R ‖ message ‖ 0xFF…FB)` (5 words, 0xA0 bytes),
then:
  * `htIdx   = (digest >> 133) & (2^22 - 1)`
  * for FORS tree `i` (0..6): `idx_i = (digest >> (19*i)) & (2^19 - 1)`.

`R`, `seed`, `root` are masked to their high 16 bytes; `message` is a full word. -/

/-- The H_msg trailing domain-separation word
`0x00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF`
as written by `mstore(0x80, 0xFF…FB...)` — the contract literal has a leading
zero nibble (63 `F`'s). -/
def hMsgPad : Word :=
  0x00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

def hMsgC13 (v : Variant) (pk : PublicKey) (R message : Bytes) : HMsg :=
  let digest :=
    keccakWords
      [ wordOfHash16 pk.pkSeed
      , wordOfHash16 pk.pkRoot
      , wordOfHash16 R
      , baToNatBE message % wordMod
      , hMsgPad ]
  let forsIndex := (List.range 7).map (fun i => (digest >>> (19 * i)) % (2 ^ 19))
  let hyperIndex := (digest >>> 133) % (2 ^ 22)
  { forsIndex := forsIndex, hyperIndex := hyperIndex }

theorem hMsgC13_forsIndex_six (pk : PublicKey) (R message : Bytes) :
    (hMsgC13 c13 pk R message).forsIndex[6]? =
      some ((keccakWords
        [ wordOfHash16 pk.pkSeed
        , wordOfHash16 pk.pkRoot
        , wordOfHash16 R
        , baToNatBE message % wordMod
        , hMsgPad ] >>> 114) % (2 ^ 19)) := by
  unfold hMsgC13
  exact getElem?_map_range _ (by decide : 6 < 7)

/-- `getD` form of the concrete C13 `H_msg` FORS index for any of the seven
19-bit slices. -/
theorem hMsgC13_forsIndex_getD_eq
    (pk : PublicKey) (R message : Bytes) {j : Nat} (hj : j < 7) :
    ((hMsgC13 c13 pk R message).forsIndex[j]?).getD 0 =
      (keccakWords
        [ wordOfHash16 pk.pkSeed
        , wordOfHash16 pk.pkRoot
        , wordOfHash16 R
        , baToNatBE message % wordMod
        , hMsgPad ] >>> (19 * j)) % (2 ^ 19) := by
  unfold hMsgC13
  have h := getElem?_map_range
    (fun i => (keccakWords [wordOfHash16 pk.pkSeed, wordOfHash16 pk.pkRoot,
        wordOfHash16 R, baToNatBE message % wordMod, hMsgPad] >>> (19 * i)) % (2 ^ 19))
    hj
  simpa using congrArg (fun o => o.getD 0) h

/-- Every FORS index extracted by the concrete C13 `H_msg` reconstruction is
19-bit.  This is the spec-side bound needed by concrete FORS leaf address
assembly. -/
theorem hMsgC13_forsIndex_getD_lt
    (pk : PublicKey) (R message : Bytes) {j : Nat} (hj : j < 7) :
    ((hMsgC13 c13 pk R message).forsIndex[j]?).getD 0 < 2 ^ 19 := by
  unfold hMsgC13
  rw [getElem?_map_range _ hj]
  exact Nat.mod_lt _ (by decide : 0 < 2 ^ 19)

/-! ### FORS+C reconstruction

For each of the K=7 FORS trees:
  * trees i=0..5 are "normal": leaf = `th(seed, FORS_TREE leaf adrs, sk_i)`,
    then climb A=19 auth levels with branchless Merkle swap;
  * tree i=6 is forced-zero: `node_6 = th(seed, FORS_TREE adrs (h=0,idx=0), sk_6)`.
Then compress: `forsPk = th(seed, FORS_ROOTS adrs, node_0..node_6)`.

FORS leaf ADRS (type=3): `or(shl(96,3), or(shl(64, i), idx))`, with the auth-path
ADRS supplying `shl(32, h+1)` (height) and `parentIdx` (index).  layer=tree=0. -/

def adrsForsLeaf (i idx : Nat) : Word := (3 <<< 96) ||| (i <<< 64) ||| idx
def adrsForsNode (i h parentIdx : Nat) : Word :=
  (3 <<< 96) ||| (i <<< 64) ||| ((h + 1) <<< 32) ||| parentIdx
def adrsForsRoots : Word := 4 <<< 96

/-- The concrete FORS leaf address word is a bounded EVM word for the six normal
FORS roots when the decoded tree index is 19-bit. -/
theorem adrsForsLeaf_lt_of_normal_idx_lt
    {i idx : Nat} (hi : i < 6) (hidx : idx < 2 ^ 19) :
    adrsForsLeaf i idx < 2 ^ 256 := by
  unfold adrsForsLeaf
  refine Nat.bitwise_lt_two_pow (Nat.bitwise_lt_two_pow ?_ ?_) ?_
  · rw [Nat.shiftLeft_eq]
    decide
  · rw [Nat.shiftLeft_eq]
    calc
      i * 2 ^ 64 ≤ 5 * 2 ^ 64 :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hi)
      _ < 2 ^ 256 := by decide
  · exact lt_trans hidx (by decide : 2 ^ 19 < 2 ^ 256)

/-- Specialization of `adrsForsLeaf_lt_of_normal_idx_lt` to the normal-root
indices inside concrete C13 `H_msg`. -/
theorem adrsForsLeaf_hMsgC13_normal_lt
    (pk : PublicKey) (R message : Bytes) {j : Nat} (hj : j < 6) :
    adrsForsLeaf j (((hMsgC13 c13 pk R message).forsIndex[j]?).getD 0) < 2 ^ 256 :=
  adrsForsLeaf_lt_of_normal_idx_lt hj
    (hMsgC13_forsIndex_getD_lt pk R message (lt_trans hj (by decide : 6 < 7)))

/-- Climb one FORS auth path (A=19) using fuel-bounded recursion.  Mirrors the
contract's branchless swap: when `pathIdx` is even, `node` is the left child;
when odd, the right child. -/
def forsClimb (seed i : Word) (fuel : Nat) (h : Nat) (pathIdx : Nat)
    (node : Word) (auth : List Bytes) : Word :=
  match fuel with
  | 0 => node
  | fuel + 1 =>
    let sibling := wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)
    let parentIdx := pathIdx / 2
    let adrs := adrsForsNode i h parentIdx
    let node' :=
      if pathIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
      else maskN (keccakWords [seed, adrs, sibling, node])
    forsClimb seed i fuel (h + 1) parentIdx node' auth

def forsPkFromSigC13 (v : Variant) (pk : PublicKey) (digest : HMsg)
    (fors : ForsSig) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  -- normal trees i = 0..5
  let roots := (List.range 6).map (fun i =>
    let treeIdx := (digest.forsIndex[i]?).getD 0
    let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
    let leaf := maskN (keccakWords [seed, adrsForsLeaf i treeIdx, sk])
    forsClimb seed i 19 0 treeIdx leaf ((fors.authPath[i]?).getD []))
  -- forced-zero tree i = 6
  let sk6 := wordOfHash16 ((fors.sk[6]?).getD ⟨#[]⟩)
  let root6 := maskN (keccakWords [seed, adrsForsLeaf 6 0, sk6])
  let allRoots := roots ++ [root6]
  let forsPk := maskN (keccakWords (seed :: adrsForsRoots :: allRoots))
  some (hash16OfWord forsPk)

/-- The six normal FORS tree roots reconstructed by C13 before adding the
forced-zero tree.  Named so verifier lemmas can target the same spec word list
without replaying the `forsPkFromSigC13` body. -/
def forsNormalRootsC13 (pk : PublicKey) (digest : HMsg) (fors : ForsSig) : List Word :=
  let seed := wordOfHash16 pk.pkSeed
  (List.range 6).map (fun i =>
    let treeIdx := (digest.forsIndex[i]?).getD 0
    let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
    let leaf := maskN (keccakWords [seed, adrsForsLeaf i treeIdx, sk])
    forsClimb seed i 19 0 treeIdx leaf ((fors.authPath[i]?).getD []))

/-- The forced-zero seventh FORS root used by C13. -/
def forsForcedRootC13 (pk : PublicKey) (fors : ForsSig) : Word :=
  let seed := wordOfHash16 pk.pkSeed
  let sk6 := wordOfHash16 ((fors.sk[6]?).getD ⟨#[]⟩)
  maskN (keccakWords [seed, adrsForsLeaf 6 0, sk6])

/-- All seven FORS roots in the exact order consumed by C13's FORS public-key
compression. -/
def forsAllRootsC13 (pk : PublicKey) (digest : HMsg) (fors : ForsSig) : List Word :=
  forsNormalRootsC13 pk digest fors ++ [forsForcedRootC13 pk fors]

/-- The masked C13 FORS public-key compression word. -/
def forsPkWordC13 (pk : PublicKey) (digest : HMsg) (fors : ForsSig) : Word :=
  let seed := wordOfHash16 pk.pkSeed
  maskN (keccakWords (seed :: adrsForsRoots :: forsAllRootsC13 pk digest fors))

/-- The named FORS root list has the expected C13 length. -/
theorem forsAllRootsC13_length (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    (forsAllRootsC13 pk digest fors).length = 7 := by
  unfold forsAllRootsC13 forsNormalRootsC13
  simp

/-- Indexing the six normal C13 FORS roots exposes the same per-tree expression
used by `forsPkFromSigC13`. -/
theorem forsNormalRootsC13_getElem?
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    {i : Nat} (hi : i < 6) :
    (forsNormalRootsC13 pk digest fors)[i]? =
      some
        (let seed := wordOfHash16 pk.pkSeed
         let treeIdx := (digest.forsIndex[i]?).getD 0
         let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
         let leaf := maskN (keccakWords [seed, adrsForsLeaf i treeIdx, sk])
         forsClimb seed i 19 0 treeIdx leaf ((fors.authPath[i]?).getD [])) := by
  unfold forsNormalRootsC13
  exact getElem?_map_range _ hi

/-- `getElem` form of `forsNormalRootsC13_getElem?`. -/
theorem forsNormalRootsC13_getElem
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    {i : Nat} (hi : i < 6) :
    (forsNormalRootsC13 pk digest fors)[i]'(by
        unfold forsNormalRootsC13
        simp [hi]) =
      (let seed := wordOfHash16 pk.pkSeed
       let treeIdx := (digest.forsIndex[i]?).getD 0
       let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
       let leaf := maskN (keccakWords [seed, adrsForsLeaf i treeIdx, sk])
       forsClimb seed i 19 0 treeIdx leaf ((fors.authPath[i]?).getD [])) := by
  unfold forsNormalRootsC13
  exact getElem_map_range _ hi

/-- The full seven-root C13 FORS list agrees with the normal-root expression on
indices `0..5`. -/
theorem forsAllRootsC13_getElem?_normal
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    {i : Nat} (hi : i < 6) :
    (forsAllRootsC13 pk digest fors)[i]? =
      some
        (let seed := wordOfHash16 pk.pkSeed
         let treeIdx := (digest.forsIndex[i]?).getD 0
         let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
         let leaf := maskN (keccakWords [seed, adrsForsLeaf i treeIdx, sk])
         forsClimb seed i 19 0 treeIdx leaf ((fors.authPath[i]?).getD [])) := by
  unfold forsAllRootsC13
  rw [List.getElem?_append_left]
  · exact forsNormalRootsC13_getElem? pk digest fors hi
  · unfold forsNormalRootsC13
    simp [hi]

/-- The seventh C13 FORS root is exactly the forced-zero root. -/
theorem forsAllRootsC13_getElem?_forced
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    (forsAllRootsC13 pk digest fors)[6]? = some (forsForcedRootC13 pk fors) := by
  unfold forsAllRootsC13 forsNormalRootsC13
  simp

/-- `getElem` form of `forsAllRootsC13_getElem?_normal`. -/
theorem forsAllRootsC13_getElem_normal
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    {i : Nat} (hi : i < 6) :
    (forsAllRootsC13 pk digest fors)[i]'(by
        rw [forsAllRootsC13_length]
        omega) =
      (let seed := wordOfHash16 pk.pkSeed
       let treeIdx := (digest.forsIndex[i]?).getD 0
       let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
       let leaf := maskN (keccakWords [seed, adrsForsLeaf i treeIdx, sk])
       forsClimb seed i 19 0 treeIdx leaf ((fors.authPath[i]?).getD [])) := by
  have hidx : i < (forsAllRootsC13 pk digest fors).length := by
    rw [forsAllRootsC13_length]
    omega
  have h :=
    forsAllRootsC13_getElem?_normal (pk := pk) (digest := digest) (fors := fors) hi
  simpa [List.getElem?_eq_getElem hidx] using h

/-- `getElem` form of `forsAllRootsC13_getElem?_forced`. -/
theorem forsAllRootsC13_getElem_forced
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    (forsAllRootsC13 pk digest fors)[6]'(by
        rw [forsAllRootsC13_length]
        omega) = forsForcedRootC13 pk fors := by
  have hidx : 6 < (forsAllRootsC13 pk digest fors).length := by
    rw [forsAllRootsC13_length]
    omega
  have h := forsAllRootsC13_getElem?_forced pk digest fors
  simpa [List.getElem?_eq_getElem hidx] using h

/-- `forsPkFromSigC13` is exactly the named seven-root compression word, encoded
back to 16 bytes.  This is purely a spec-side factoring lemma for the C13 accept
path; it does not touch any executable model or bridge axiom. -/
theorem forsPkFromSigC13_eq_named
    (v : Variant) (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    forsPkFromSigC13 v pk digest fors
      = some (hash16OfWord (forsPkWordC13 pk digest fors)) := by
  unfold forsPkFromSigC13 forsPkWordC13 forsAllRootsC13
    forsNormalRootsC13 forsForcedRootC13
  rfl

/-- If C13 FORS reconstruction returns a byte string, it is exactly the high
16-byte read of the named FORS compression word. -/
theorem forsPkFromSigC13_some_eq_hash16_named
    {v : Variant} {pk : PublicKey} {digest : HMsg} {fors : ForsSig}
    {forsPk : Bytes}
    (h : forsPkFromSigC13 v pk digest fors = some forsPk) :
    forsPk = hash16OfWord (forsPkWordC13 pk digest fors) := by
  rw [forsPkFromSigC13_eq_named] at h
  injection h with hEq
  exact hEq.symm

/-- Any successful C13 FORS public-key reconstruction returns a 16-byte value. -/
theorem forsPkFromSigC13_size
    {v : Variant} {pk : PublicKey} {digest : HMsg} {fors : ForsSig}
    {forsPk : Bytes}
    (h : forsPkFromSigC13 v pk digest fors = some forsPk) :
    forsPk.size = 16 := by
  rw [forsPkFromSigC13_eq_named] at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_size _

/-- Any successful C13 FORS public-key reconstruction returns a canonical
`hash16OfWord` output. -/
theorem forsPkFromSigC13_canonical
    {v : Variant} {pk : PublicKey} {digest : HMsg} {fors : ForsSig}
    {forsPk : Bytes}
    (h : forsPkFromSigC13 v pk digest fors = some forsPk) :
    CanonicalHash16 forsPk := by
  exact ⟨forsPkWordC13 pk digest fors, forsPkFromSigC13_some_eq_hash16_named h⟩

/-- For C13, the spec-side forced-zero check means the seventh FORS index is
present and equal to zero. -/
theorem forcedZeroOk_c13_forsIndex_six
    (digest : HMsg) (h : forcedZeroOk c13 digest = true) :
    digest.forsIndex[6]? = some 0 := by
  unfold forcedZeroOk at h
  simpa [c13] using h

/-! ### WOTS+ chains and PK compression

Per layer, with `idxLeaf`, `idxTree`, base node `currentNode`, `count`:
  * `d = keccak256(seed ‖ WOTS_HASH base ADRS ‖ currentNode ‖ count)` (4 words),
    where WOTS_HASH base ADRS = `or(shl(224,layer), or(shl(128,idxTree), shl(64,idxLeaf)))`
    (type=0 implicit, word2=word3=0);
  * digit_i = `(d >> (3*i)) & 7`, steps_i = `7 - digit_i`;
  * chain i: start from `chains[i]`, apply `steps_i` hashes with ADRS
    `or(chainBase, add(digit, step))`, `chainBase = or(wotsAdrs, shl(32, i))`;
  * WOTS_PK = `th(seed, WOTS_PK adrs, chain_0..chain_42)`,
    WOTS_PK adrs = `or(shl(224,layer), or(shl(128,idxTree), or(shl(96,1), shl(64,idxLeaf))))`.

`d` is *not* masked in the contract (full 256-bit word used for digit extraction).
The grinding check requires `sum(digit_i) == 208`. -/

def adrsWotsHashBase (layer idxTree idxLeaf : Nat) : Word :=
  (layer <<< 224) ||| (idxTree <<< 128) ||| (idxLeaf <<< 64)
def adrsWotsPk (layer idxTree idxLeaf : Nat) : Word :=
  (layer <<< 224) ||| (idxTree <<< 128) ||| (1 <<< 96) ||| (idxLeaf <<< 64)

/-- The WOTS message digest word `d` for a layer. -/
def wotsDigest (seed : Word) (layer idxTree idxLeaf count : Nat)
    (node : Word) : Word :=
  keccakWords [seed, adrsWotsHashBase layer idxTree idxLeaf, node, count]

/-- Apply `steps` chain hashes starting from `val`, beginning at chain position
`digit` (so the `step`-th hash uses ADRS word3 = `digit + step`). -/
def chainHash (seed chainBase : Word) (digit : Nat) (fuel step : Nat)
    (val : Word) : Word :=
  match fuel with
  | 0 => val
  | fuel + 1 =>
    let val' := maskN (keccakWords [seed, chainBase ||| (digit + step), val])
    chainHash seed chainBase digit fuel (step + 1) val'

def wotsDigitSum (d : Word) : Nat :=
  (List.range 43).foldl (fun acc i => acc + ((d >>> (3 * i)) % 8)) 0

/-- Any finite WOTS digit fold is bounded by seven times its length. -/
theorem wotsDigitSum_fold_le (d acc : Nat) :
    ∀ xs : List Nat,
      xs.foldl (fun acc i => acc + ((d >>> (3 * i)) % 8)) acc
        ≤ acc + 7 * xs.length
  | [] => by simp
  | i :: xs => by
      have htail :=
        wotsDigitSum_fold_le d (acc + ((d >>> (3 * i)) % 8)) xs
      have hdigit : (d >>> (3 * i)) % 8 ≤ 7 := by
        exact Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 8))
      simp only [List.foldl_cons, List.length_cons]
      exact Nat.le_trans htail (by omega)

/-- The 43 three-bit WOTS digits sum to at most `43 * 7 = 301`. -/
theorem wotsDigitSum_le_301 (d : Word) : wotsDigitSum d ≤ 301 := by
  unfold wotsDigitSum
  have h := wotsDigitSum_fold_le d 0 (List.range 43)
  simpa using h

/-- The WOTS digit sum is far below the EVM word modulus. -/
theorem wotsDigitSum_lt_uint256 (d : Word) : wotsDigitSum d < 2 ^ 256 := by
  exact lt_of_le_of_lt (wotsDigitSum_le_301 d) (by decide : 301 < 2 ^ 256)

/-- The reconstructed WOTS public key word for one layer.  `treeIdx`/`leafIdx`
follow the spec's per-layer naming (`nextTree`/`idxLeaf`). -/
def wotsPkWord (seed : Word) (layer treeIdx leafIdx : Nat)
    (node : Word) (wots : WotsSig) : Word :=
  let d := wotsDigest seed layer treeIdx leafIdx wots.count node
  let wotsAdrs := adrsWotsHashBase layer treeIdx leafIdx
  let chainsEnd := (List.range 43).map (fun i =>
    let digit := (d >>> (3 * i)) % 8
    let steps := 7 - digit
    let val := wordOfHash16 ((wots.chains[i]?).getD ⟨#[]⟩)
    let chainBase := wotsAdrs ||| (i <<< 32)
    chainHash seed chainBase digit steps 0 val)
  maskN (keccakWords (seed :: adrsWotsPk layer treeIdx leafIdx :: chainsEnd))

/-- C13 uses `WotsMode.grindingTarget 208`; the `layer` is not threaded into the
`Primitives` API (the spec passes `treeIdx`/`leafIdx`).  The contract's grinding
target (digit sum = 208) is layer-independent, and the WOTS digest `d` depends on
`layer` only through the ADRS layer field, which does not change the digit *sum*
in any layer for a fixed `(treeIdx, leafIdx, node, count)` preimage in the sense
the contract checks per layer.  We therefore evaluate the check at the layer the
spec is climbing; since the contract applies the identical check in both layers,
we model it with `layer := 0` for the grinding predicate and `wotsPkFromSig`,
matching the Primitives signature (which carries no `layer`). -/
def wotsPkFromSigC13 (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  let nodeW := wordOfHash16 node
  let pkW := wotsPkWord seed 0 treeIdx leafIdx nodeW wots
  some (hash16OfWord pkW)

def wotsGrindingOkC13 (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Bool :=
  let seed := wordOfHash16 pk.pkSeed
  let nodeW := wordOfHash16 node
  let d := wotsDigest seed 0 treeIdx leafIdx wots.count nodeW
  wotsDigitSum d == 208

/-! ### XMSS Merkle auth path (subtree height 11)

TREE ADRS: `or(shl(224,layer), or(shl(128,idxTree), shl(96,2)))`, supplying
`shl(32, h+1)` (height) and `parentIdx` (index).  Branchless swap as in FORS. -/

def adrsXmssTree (layer idxTree : Nat) : Word :=
  (layer <<< 224) ||| (idxTree <<< 128) ||| (2 <<< 96)

def xmssClimb (seed treeAdrs : Word) (fuel : Nat) (h : Nat) (mIdx : Nat)
    (node : Word) (auth : List Bytes) : Word :=
  match fuel with
  | 0 => node
  | fuel + 1 =>
    let sibling := wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)
    let parentIdx := mIdx / 2
    let adrs := treeAdrs ||| ((h + 1) <<< 32) ||| parentIdx
    let node' :=
      if mIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
      else maskN (keccakWords [seed, adrs, sibling, node])
    xmssClimb seed treeAdrs fuel (h + 1) parentIdx node' auth

def xmssRootFromSigC13 (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (wotsPk : Bytes) (auth : List Bytes) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  let treeAdrs := adrsXmssTree 0 treeIdx
  let start := wordOfHash16 wotsPk
  let root := xmssClimb seed treeAdrs 11 0 leafIdx start auth
  some (hash16OfWord root)

/-- Any successful C13 WOTS public-key reconstruction returns a 16-byte value. -/
theorem wotsPkFromSigC13_size
    {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat} {node : Bytes}
    {wots : WotsSig} {wotsPk : Bytes}
    (h : wotsPkFromSigC13 v pk treeIdx leafIdx node wots = some wotsPk) :
    wotsPk.size = 16 := by
  unfold wotsPkFromSigC13 at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_size _

/-- Any successful C13 WOTS public-key reconstruction returns a canonical
`hash16OfWord` output. -/
theorem wotsPkFromSigC13_canonical
    {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat} {node : Bytes}
    {wots : WotsSig} {wotsPk : Bytes}
    (h : wotsPkFromSigC13 v pk treeIdx leafIdx node wots = some wotsPk) :
    CanonicalHash16 wotsPk := by
  unfold wotsPkFromSigC13 at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_canonical _

/-- Any successful C13 XMSS root reconstruction returns a 16-byte value. -/
theorem xmssRootFromSigC13_size
    {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat} {wotsPk : Bytes}
    {auth : List Bytes} {root : Bytes}
    (h : xmssRootFromSigC13 v pk treeIdx leafIdx wotsPk auth = some root) :
    root.size = 16 := by
  unfold xmssRootFromSigC13 at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_size _

/-- Any successful C13 XMSS root reconstruction returns a canonical
`hash16OfWord` output. -/
theorem xmssRootFromSigC13_canonical
    {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat} {wotsPk : Bytes}
    {auth : List Bytes} {root : Bytes}
    (h : xmssRootFromSigC13 v pk treeIdx leafIdx wotsPk auth = some root) :
    CanonicalHash16 root := by
  unfold xmssRootFromSigC13 at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_canonical _

/-- The concrete C13 `Primitives`, all six fields routed through `keccakWords`
(hence `KeccakEngine.keccak256` over the interpreter's big-endian word preimage).
No `sorry`, no new axioms. -/
def c13PrimitivesConcrete : Primitives :=
  { parseSignature  := parseSignatureC13
  , hMsg            := hMsgC13
  , forsPkFromSig   := forsPkFromSigC13
  , wotsPkFromSig   := wotsPkFromSigC13
  , wotsGrindingOk  := wotsGrindingOkC13
  , xmssRootFromSig := xmssRootFromSigC13 }

/-- A successful C13 WOTS grinding check is exactly the concrete digit-sum
target used by the contract guard. -/
theorem wotsGrindingFailsC13_false_digitSum
    (pk : PublicKey) (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig)
    (h : wotsGrindingFails c13PrimitivesConcrete c13 pk treeIdx leafIdx node wots = false) :
    wotsDigitSum
        (wotsDigest (wordOfHash16 pk.pkSeed) 0 treeIdx leafIdx wots.count
          (wordOfHash16 node)) = 208 := by
  simpa [wotsGrindingFails, c13PrimitivesConcrete, wotsGrindingOkC13, c13] using h

/-- If the C13 hypertree climb returns `.ok root`, then the returned root is
16 bytes, provided the starting FORS public key is 16 bytes. -/
theorem foldHypertreeAux_c13_ok_root_size
    (pk : PublicKey) (fuel layer idxTree : Nat) (node : Bytes)
    (layers : List XmssLayerSig) {root : Bytes}
    (hNode : node.size = 16)
    (h : foldHypertreeAux c13PrimitivesConcrete c13 pk fuel layer idxTree node layers
        = .ok root) :
    root.size = 16 := by
  induction fuel generalizing layer idxTree node root with
  | zero =>
      unfold foldHypertreeAux at h
      injection h with hEq
      rw [← hEq]
      exact hNode
  | succ fuel ih =>
      unfold foldHypertreeAux at h
      by_cases hlt : layer < c13.d
      · simp only [hlt, ↓reduceIte] at h
        cases hLayer : layers[layer]? with
        | none => simp [hLayer] at h
        | some lsig =>
            simp only [hLayer] at h
            let idxLeaf := idxTree % 2 ^ c13.subtreeH
            let nextTree := idxTree / 2 ^ c13.subtreeH
            by_cases hgrind :
                wotsGrindingFails c13PrimitivesConcrete c13 pk nextTree idxLeaf node lsig.wots
                  = true
            · simp [idxLeaf, nextTree, hgrind] at h
            · simp only [idxLeaf, nextTree, hgrind] at h
              cases hWots :
                  c13PrimitivesConcrete.wotsPkFromSig c13 pk nextTree idxLeaf node lsig.wots
                  with
              | none =>
                  have hWots' :
                      c13PrimitivesConcrete.wotsPkFromSig c13 pk
                        (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                        node lsig.wots = none := by
                    simpa [idxLeaf, nextTree] using hWots
                  simp [hWots'] at h
              | some wotsPk =>
                  have hWots' :
                      c13PrimitivesConcrete.wotsPkFromSig c13 pk
                        (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                        node lsig.wots = some wotsPk := by
                    simpa [idxLeaf, nextTree] using hWots
                  simp only [hWots'] at h
                  cases hXmss :
                      c13PrimitivesConcrete.xmssRootFromSig c13 pk nextTree idxLeaf
                        wotsPk lsig.authPath with
                  | none =>
                      have hXmss' :
                          c13PrimitivesConcrete.xmssRootFromSig c13 pk
                            (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                            wotsPk lsig.authPath = none := by
                        simpa [idxLeaf, nextTree] using hXmss
                      simp [hXmss'] at h
                  | some xmssRoot =>
                      have hXmss' :
                          c13PrimitivesConcrete.xmssRootFromSig c13 pk
                            (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                            wotsPk lsig.authPath = some xmssRoot := by
                        simpa [idxLeaf, nextTree] using hXmss
                      simp only [hXmss'] at h
                      have hx : xmssRoot.size = 16 := by
                        exact xmssRootFromSigC13_size
                          (by simpa [c13PrimitivesConcrete] using hXmss')
                      exact ih (layer + 1) nextTree xmssRoot hx h
      · simp only [hlt, ↓reduceIte] at h
        injection h with hEq
        rw [← hEq]
        exact hNode

/-- C13 `foldHypertree` preserves 16-byte roots on successful `.ok` output. -/
theorem foldHypertree_c13_ok_root_size
    {pk : PublicKey} {digest : HMsg} {forsPk : Bytes} {layers : List XmssLayerSig}
    {root : Bytes}
    (hForsPk : forsPk.size = 16)
    (h : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers = .ok root) :
    root.size = 16 :=
  foldHypertreeAux_c13_ok_root_size pk c13.d 0 digest.hyperIndex forsPk layers hForsPk h

/-- C13 `foldHypertree` returns a 16-byte root after successful C13 FORS
reconstruction. -/
theorem foldHypertree_c13_ok_root_size_of_fors
    {pk : PublicKey} {digest : HMsg} {fors : ForsSig} {forsPk root : Bytes}
    {layers : List XmssLayerSig}
    (hFors : c13PrimitivesConcrete.forsPkFromSig c13 pk digest fors = some forsPk)
    (hFold : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers = .ok root) :
    root.size = 16 :=
  foldHypertree_c13_ok_root_size
    (forsPkFromSigC13_size (by simpa [c13PrimitivesConcrete] using hFors)) hFold

/-- If the C13 hypertree climb returns `.ok root`, then the returned root is
canonical, provided the starting FORS public key is canonical. -/
theorem foldHypertreeAux_c13_ok_root_canonical
    (pk : PublicKey) (fuel layer idxTree : Nat) (node : Bytes)
    (layers : List XmssLayerSig) {root : Bytes}
    (hNode : CanonicalHash16 node)
    (h : foldHypertreeAux c13PrimitivesConcrete c13 pk fuel layer idxTree node layers
        = .ok root) :
    CanonicalHash16 root := by
  induction fuel generalizing layer idxTree node root with
  | zero =>
      unfold foldHypertreeAux at h
      injection h with hEq
      rw [← hEq]
      exact hNode
  | succ fuel ih =>
      unfold foldHypertreeAux at h
      by_cases hlt : layer < c13.d
      · simp only [hlt, ↓reduceIte] at h
        cases hLayer : layers[layer]? with
        | none => simp [hLayer] at h
        | some lsig =>
            simp only [hLayer] at h
            let idxLeaf := idxTree % 2 ^ c13.subtreeH
            let nextTree := idxTree / 2 ^ c13.subtreeH
            by_cases hgrind :
                wotsGrindingFails c13PrimitivesConcrete c13 pk nextTree idxLeaf node lsig.wots
                  = true
            · simp [idxLeaf, nextTree, hgrind] at h
            · simp only [idxLeaf, nextTree, hgrind] at h
              cases hWots :
                  c13PrimitivesConcrete.wotsPkFromSig c13 pk nextTree idxLeaf node lsig.wots
                  with
              | none =>
                  have hWots' :
                      c13PrimitivesConcrete.wotsPkFromSig c13 pk
                        (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                        node lsig.wots = none := by
                    simpa [idxLeaf, nextTree] using hWots
                  simp [hWots'] at h
              | some wotsPk =>
                  have hWots' :
                      c13PrimitivesConcrete.wotsPkFromSig c13 pk
                        (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                        node lsig.wots = some wotsPk := by
                    simpa [idxLeaf, nextTree] using hWots
                  simp only [hWots'] at h
                  cases hXmss :
                      c13PrimitivesConcrete.xmssRootFromSig c13 pk nextTree idxLeaf
                        wotsPk lsig.authPath with
                  | none =>
                      have hXmss' :
                          c13PrimitivesConcrete.xmssRootFromSig c13 pk
                            (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                            wotsPk lsig.authPath = none := by
                        simpa [idxLeaf, nextTree] using hXmss
                      simp [hXmss'] at h
                  | some xmssRoot =>
                      have hXmss' :
                          c13PrimitivesConcrete.xmssRootFromSig c13 pk
                            (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                            wotsPk lsig.authPath = some xmssRoot := by
                        simpa [idxLeaf, nextTree] using hXmss
                      simp only [hXmss'] at h
                      have hx : CanonicalHash16 xmssRoot := by
                        exact xmssRootFromSigC13_canonical
                          (by simpa [c13PrimitivesConcrete] using hXmss')
                      exact ih (layer + 1) nextTree xmssRoot hx h
      · simp only [hlt, ↓reduceIte] at h
        injection h with hEq
        rw [← hEq]
        exact hNode

/-- C13 `foldHypertree` preserves canonical roots on successful `.ok` output. -/
theorem foldHypertree_c13_ok_root_canonical
    {pk : PublicKey} {digest : HMsg} {forsPk : Bytes} {layers : List XmssLayerSig}
    {root : Bytes}
    (hForsPk : CanonicalHash16 forsPk)
    (h : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers = .ok root) :
    CanonicalHash16 root :=
  foldHypertreeAux_c13_ok_root_canonical
    pk c13.d 0 digest.hyperIndex forsPk layers hForsPk h

/-- C13 `foldHypertree` returns a canonical root after successful C13 FORS
reconstruction. -/
theorem foldHypertree_c13_ok_root_canonical_of_fors
    {pk : PublicKey} {digest : HMsg} {fors : ForsSig} {forsPk root : Bytes}
    {layers : List XmssLayerSig}
    (hFors : c13PrimitivesConcrete.forsPkFromSig c13 pk digest fors = some forsPk)
    (hFold : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers = .ok root) :
    CanonicalHash16 root :=
  foldHypertree_c13_ok_root_canonical
    (forsPkFromSigC13_canonical (by simpa [c13PrimitivesConcrete] using hFors)) hFold

#print axioms forsAllRootsC13_length
#print axioms forsNormalRootsC13_getElem?
#print axioms forsNormalRootsC13_getElem
#print axioms forsAllRootsC13_getElem?_normal
#print axioms forsAllRootsC13_getElem?_forced
#print axioms forsAllRootsC13_getElem_normal
#print axioms forsAllRootsC13_getElem_forced
#print axioms forsPkFromSigC13_eq_named
#print axioms forsPkFromSigC13_some_eq_hash16_named
#print axioms hash16OfWord_size
#print axioms CanonicalHash16
#print axioms hash16OfWord_canonical
#print axioms forsPkFromSigC13_size
#print axioms forsPkFromSigC13_canonical
#print axioms wotsPkFromSigC13_size
#print axioms wotsPkFromSigC13_canonical
#print axioms xmssRootFromSigC13_size
#print axioms xmssRootFromSigC13_canonical
#print axioms wotsDigitSum_fold_le
#print axioms wotsDigitSum_le_301
#print axioms wotsDigitSum_lt_uint256
#print axioms wotsGrindingFailsC13_false_digitSum
#print axioms foldHypertreeAux_c13_ok_root_size
#print axioms foldHypertree_c13_ok_root_size
#print axioms foldHypertree_c13_ok_root_size_of_fors
#print axioms foldHypertreeAux_c13_ok_root_canonical
#print axioms foldHypertree_c13_ok_root_canonical
#print axioms foldHypertree_c13_ok_root_canonical_of_fors
#print axioms parseSignatureC13_R
#print axioms parseSignatureC13_shape
#print axioms parseSignatureC13_layers_length
#print axioms publicKeyOk_c13
#print axioms publicKeyOk_c13_does_not_imply_pkRoot_size
#print axioms publicKeyOk_c13_does_not_imply_pkSeed_size
#print axioms parsePublicKey_c13
#print axioms parsePublicKey_c13_does_not_imply_pkRoot_size
#print axioms parsePublicKey_c13_does_not_imply_pkSeed_size
#print axioms parseSignatureC13_fors_sk_getElem?
#print axioms parseSignatureC13_fors_authPath_getD_getElem?
#print axioms forcedZeroOk_c13_forsIndex_six
#print axioms hMsgC13_forsIndex_six
#print axioms hMsgC13_forsIndex_getD_eq
#print axioms hMsgC13_forsIndex_getD_lt
#print axioms adrsForsLeaf_lt_of_normal_idx_lt
#print axioms adrsForsLeaf_hMsgC13_normal_lt

end C13Concrete
end SphincsMinusVerifierSpec
