/-
  Concrete C12 `Primitives` package (Phase 0).

  This file replaces the *opaque* `axiom c12Primitives : Primitives` with a
  concrete `def c12PrimitivesConcrete : Primitives` whose hashing is routed
  through the SAME pure Keccak the Verity interpreter uses, fed the SAME
  big-endian word-aligned byte preimage — exactly as `C13Concrete` does for C13.

  It mirrors the structure of `C13Concrete`, REUSING the generic n=128 Keccak
  kernel verbatim (`keccakWords`, `maskN`, `wordOfHash16`, `hash16OfWord`,
  `baToNatBE`, `read16`, `xmssClimb`), and rewrites only the C12-specific parts
  to match the compiled body `c12VerifyBody` in `SphincsMinusVerifiers/Model.lean`
  (lines ~232-345).  Where the C12 body diverges from C13:

    * ADRS layout is the JARDIN 32-byte format (different bit-shifts).
    * Params: h=20, d=5, a=7, k=20 FORS trees, w=8, l=45 WOTS chains
      (42 message digits + 3 checksum digits), XMSS subtree height h'=4.
    * WOTS uses a REAL base-8 checksum (`csum = Σ (7 - digit)` over 42 digits,
      then 3 checksum digits from `csum << 7`), NOT C13's grinding target.
      C12 `wotsMode = standardChecksum`, so the spec never consults
      `wotsGrindingOk` (`wotsGrindingFails` short-circuits on `standardChecksum`);
      we return `true` there.  The checksum is computed *inside* `wotsPkFromSig`
      because it determines the chain step counts.
    * WOTS chain ADRS shifts the chain position by 32 bits
      (`chainBase | ((digit+s) << 32)`), unlike C13.
    * Signature layout is 6512 bytes; R is the FULL 32-byte word (unmasked).
    * H_msg pads with `0xFF…FC` over 0xA0 bytes and slices
      `treeIdx = (d>>140)&0xFFFF`, `leafIdx = (d>>156)&0xF`,
      `mdT = (d>>(7*t))&0x7F`.

  MODELING JUDGMENT CALL (identical to `C13Concrete`): the C12 ADRS embeds the
  hypertree `layer` in its high bits (`layer << 224`), but the `Primitives` API
  threads only `(treeIdx, leafIdx)` per layer — there is no `layer` parameter.
  We therefore evaluate the WOTS/XMSS reconstruction with `layer := 0`, matching
  the interface, exactly as `C13Concrete` does.  The MODEL-EXEC-BRIDGE remains a
  named axiom, so this gap is documented, not machine-checked here.

  It is ADDITIVE: it does not touch `axiom c12Primitives`, `execC12`, the bridge
  axioms, `Model.lean`, or any C13 code (it only `open`s `C13Concrete`
  read-only).
-/

import SphincsMinusVerifierSpec.Spec
import SphincsMinusVerifierSpec.C13Concrete
import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SphincsMinusVerifierSpec
namespace C12Concrete

open SphincsMinusVerifierSpec.C13Concrete
  (Word wordMod nMask maskN keccakBytes keccakWords baToNatBE
   wordOfHash16 hash16OfWord read16 xmssClimb)

/-! ### Read a full 32-byte word field (C12's R is unmasked, rBytes = 32) -/

/-- Read the 32-byte word at byte-offset `off` from `sig`, as a `ByteArray`. -/
def read32 (sig : Bytes) (off : Nat) : Bytes :=
  ⟨((List.range 32).map (fun i => (sig[off + i]?).getD 0)).toArray⟩

/-! ### Signature byte layout (C12, 6512 bytes)

    R                   : bytes  0..32  (FULL word at offset 0, NOT masked)
    FORS (k=20 trees), stride 128, starting at offset 32:
      sk_t              : 32 + 128*t                     (16 bytes)
      auth_t[j] (j=0..6): 48 + 128*t + 16*j              (16 bytes)
      -> FORS region 32 .. 2592
    per layer (×5), sigOff starts 2592, stride 784:
      chains[45]        : sigOff + 16*i                  -> 720 bytes
      auth[4]           : sigOff + 720 + 16*h            -> 64 bytes
      next sigOff       : sigOff + 784

All 16-byte fields are read as `and(calldataload(off), N_MASK)` (high 16 bytes);
R is read as a full word. -/

def parseSignatureC12 (v : Variant) (sig : Bytes) : Option Signature :=
  if sig.size ≠ v.sigBytes then none
  else
    let R := read32 sig 0
    let forsSk := (List.range 20).map (fun t => read16 sig (32 + 128 * t))
    let forsAuth := (List.range 20).map (fun t =>
      (List.range 7).map (fun j => read16 sig (48 + 128 * t + 16 * j)))
    let fors : ForsSig := { sk := forsSk, authPath := forsAuth }
    let layers := (List.range 5).map (fun layer =>
      let sigOff := 2592 + 784 * layer
      let chains := (List.range 45).map (fun i => read16 sig (sigOff + 16 * i))
      let auth := (List.range 4).map (fun h => read16 sig (sigOff + 720 + 16 * h))
      ({ wots := { chains := chains, count := 0 }, authPath := auth } : XmssLayerSig))
    some { R := R, fors := fors, layers := layers }

/-! ### H_msg

The contract computes
`d = keccak256(seed ‖ root ‖ R ‖ message ‖ 0xFF…FC)` (5 words, 0xA0 bytes), then:
  * `treeIdx = (d >> 140) & 0xFFFF`
  * `leafIdx = (d >> 156) & 0xF`
  * for FORS tree `t` (0..19): `mdT_t = (d >> (7*t)) & 0x7F`.

`seed`, `root` are 16-byte values injected into the high half; `R` is the FULL
32-byte word (rBytes = 32, unmasked in the body); `message` is a full word.

`hyperIndex` packs the climb walk: layer L uses tree index `treeIdx >> (4*L)` and
leaf `leafIdx` at L=0, then `(treeIdx >> 4*(L-1)) & 0xF`.  `foldHypertree` realizes
this with `idxTree := hyperIndex`, `idxLeaf := idxTree % 16`, `nextTree := idxTree / 16`,
so the matching seed is `hyperIndex = treeIdx*16 + leafIdx = (treeIdx << 4) | leafIdx`. -/

/-- The H_msg trailing domain-separation word, the contract literal
`mstore(0x80, 0xFF…FC)`. -/
def hMsgPad : Word :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC

def hMsgC12 (v : Variant) (pk : PublicKey) (R message : Bytes) : HMsg :=
  let dVal :=
    keccakWords
      [ wordOfHash16 pk.pkSeed
      , wordOfHash16 pk.pkRoot
      , baToNatBE R % wordMod
      , baToNatBE message % wordMod
      , hMsgPad ]
  let treeIdx := (dVal >>> 140) % (2 ^ 16)
  let leafIdx := (dVal >>> 156) % (2 ^ 4)
  let forsIndex := (List.range 20).map (fun t => (dVal >>> (7 * t)) % (2 ^ 7))
  let hyperIndex := (treeIdx <<< 4) ||| leafIdx
  { forsIndex := forsIndex, hyperIndex := hyperIndex }

/-! ### FORS reconstruction (JARDIN ADRS, k=20 trees, a=7 auth levels)

`forsBase = (treeIdx << 160) | (3 << 128) | (leafIdx << 96)`.
For tree `t` with message index `mdT`:
  * leaf node ADRS: `forsBase | (t << 7) | mdT`,
    leaf = `th(seed, leafAdrs, sk_t)`;
  * climb a=7 levels: at level `j` (0..6), ADRS
    `forsBase | ((j+1) << 32) | globalY`, where
    `globalY = (t << (6-j)) | parentIdx` is the global node index at that height
    across all k trees; branchless Merkle swap on `pathIdx` parity.
Then compress: `forsPk = th(seed, adrsRoots, node_0..node_19)`,
`adrsRoots = (treeIdx << 160) | (4 << 128) | (leafIdx << 96)`. -/

def adrsForsLeafC12 (forsBase t mdT : Nat) : Word := forsBase ||| (t <<< 7) ||| mdT
def adrsForsRootsC12 (treeIdx leafIdx : Nat) : Word :=
  (treeIdx <<< 160) ||| (4 <<< 128) ||| (leafIdx <<< 96)
def forsBaseC12 (treeIdx leafIdx : Nat) : Word :=
  (treeIdx <<< 160) ||| (3 <<< 128) ||| (leafIdx <<< 96)

/-- Climb one FORS auth path (a=7) for tree `t`, fuel-bounded.  Mirrors the
contract's branchless swap and the `globalY = (t << (6-j)) | parentIdx`
addressing. -/
def forsClimbC12 (seed forsBase : Word) (t : Nat) (fuel : Nat) (j : Nat)
    (pathIdx : Nat) (node : Word) (auth : List Bytes) : Word :=
  match fuel with
  | 0 => node
  | fuel + 1 =>
    let sibling := wordOfHash16 ((auth[j]?).getD ⟨#[]⟩)
    let parentIdx := pathIdx / 2
    let globalY := (t <<< (6 - j)) ||| parentIdx
    let adrs := forsBase ||| ((j + 1) <<< 32) ||| globalY
    let node' :=
      if pathIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
      else maskN (keccakWords [seed, adrs, sibling, node])
    forsClimbC12 seed forsBase t fuel (j + 1) parentIdx node' auth

def forsPkFromSigC12 (v : Variant) (pk : PublicKey) (digest : HMsg)
    (fors : ForsSig) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  let treeIdx := digest.hyperIndex >>> 4
  let leafIdx := digest.hyperIndex &&& 0xF
  let forsBase := forsBaseC12 treeIdx leafIdx
  let roots := (List.range 20).map (fun t =>
    let mdT := (digest.forsIndex[t]?).getD 0
    let sk := wordOfHash16 ((fors.sk[t]?).getD ⟨#[]⟩)
    let leaf := maskN (keccakWords [seed, adrsForsLeafC12 forsBase t mdT, sk])
    forsClimbC12 seed forsBase t 7 0 mdT leaf ((fors.authPath[t]?).getD []))
  let forsPk :=
    maskN (keccakWords (seed :: adrsForsRootsC12 treeIdx leafIdx :: roots))
  some (hash16OfWord forsPk)

/-! ### WOTS+ chains and PK compression (real base-8 checksum)

Per layer, with `treeIdx`, `leafIdx`, message node `node`:
  * `wotsBase = (layer << 224) | (treeIdx << 160) | (leafIdx << 96)`;
  * 42 message digits `digit_i = (node >> (128 + 3*i)) & 7`, steps_i = 7 - digit_i;
  * `csum = Σ_{i<42} (7 - digit_i)`, then `csumShifted = csum << 7` and
    3 checksum digits `digit_{42+j} = (csumShifted >> (13 - 3*j)) & 7`;
  * chain i: start from `chains[i]`, apply `steps_i` hashes with ADRS
    `chainBase | ((digit + step) << 32)`, `chainBase = wotsBase | (i << 64)`;
  * `WOTS_PK = th(seed, pkAdrs, chain_0..chain_44)`,
    `pkAdrs = (layer << 224) | (treeIdx << 160) | (1 << 128) | (leafIdx << 96)`.

`node >> 128` extracts the high-16-byte payload before slicing 3-bit digits, so
we read them from `wordOfHash16 node`. -/

def wotsBaseC12 (layer treeIdx leafIdx : Nat) : Word :=
  (layer <<< 224) ||| (treeIdx <<< 160) ||| (leafIdx <<< 96)
def wotsPkAdrsC12 (layer treeIdx leafIdx : Nat) : Word :=
  (layer <<< 224) ||| (treeIdx <<< 160) ||| (1 <<< 128) ||| (leafIdx <<< 96)

def wotsDigitC12 (nodeW : Word) (i : Nat) : Nat := (nodeW >>> (128 + 3 * i)) % 8

def wotsCsumC12 (nodeW : Word) : Nat :=
  (List.range 42).foldl (fun acc i => acc + (7 - wotsDigitC12 nodeW i)) 0

/-- Apply `steps` chain hashes starting from `val`, beginning at chain position
`digit` (the `step`-th hash uses ADRS word2 = `(digit + step) << 32`). -/
def chainHashC12 (seed chainBase : Word) (digit : Nat) (fuel step : Nat)
    (val : Word) : Word :=
  match fuel with
  | 0 => val
  | fuel + 1 =>
    let val' := maskN (keccakWords [seed, chainBase ||| ((digit + step) <<< 32), val])
    chainHashC12 seed chainBase digit fuel (step + 1) val'

/-- The reconstructed WOTS public key word for one layer. -/
def wotsPkWordC12 (seed : Word) (layer treeIdx leafIdx : Nat)
    (node : Word) (wots : WotsSig) : Word :=
  let wotsBase := wotsBaseC12 layer treeIdx leafIdx
  let csum := wotsCsumC12 node
  let csumShifted := csum <<< 7
  let chainsEnd := (List.range 45).map (fun i =>
    let digit :=
      if i < 42 then wotsDigitC12 node i
      else (csumShifted >>> (13 - 3 * (i - 42))) % 8
    let steps := 7 - digit
    let val := wordOfHash16 ((wots.chains[i]?).getD ⟨#[]⟩)
    let chainBase := wotsBase ||| (i <<< 64)
    chainHashC12 seed chainBase digit steps 0 val)
  maskN (keccakWords (seed :: wotsPkAdrsC12 layer treeIdx leafIdx :: chainsEnd))

/-- C12 is `WotsMode.standardChecksum`, so the spec never consults
`wotsGrindingOk` (`wotsGrindingFails` short-circuits).  `layer := 0` per the
interface limitation documented in the file header. -/
def wotsPkFromSigC12 (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  let nodeW := wordOfHash16 node
  some (hash16OfWord (wotsPkWordC12 seed 0 treeIdx leafIdx nodeW wots))

/-- Never consulted for C12 (`standardChecksum`); returns `true`. -/
def wotsGrindingOkC12 (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Bool := true

/-! ### XMSS Merkle auth path (subtree height 4)

`xmssBase = (layer << 224) | (treeIdx << 160) | (2 << 128)`, supplying
`(h+1) << 32` (height) and `parentIdx` (index).  The per-level step (adding
`(h+1) << 32` and `parentIdx`, branchless swap) is identical to C13's
`xmssClimb`, so we REUSE it with C12's `xmssBase`. -/

def xmssBaseC12 (layer treeIdx : Nat) : Word :=
  (layer <<< 224) ||| (treeIdx <<< 160) ||| (2 <<< 128)

def xmssRootFromSigC12 (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (wotsPk : Bytes) (auth : List Bytes) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  let xmssBase := xmssBaseC12 0 treeIdx
  let start := wordOfHash16 wotsPk
  let root := xmssClimb seed xmssBase 4 0 leafIdx start auth
  some (hash16OfWord root)

/-- The concrete C12 `Primitives`, all six fields routed through `keccakWords`
(hence `KeccakEngine.keccak256` over the interpreter's big-endian word preimage).
No `sorry`, no new axioms. -/
def c12PrimitivesConcrete : Primitives :=
  { parseSignature  := parseSignatureC12
  , hMsg            := hMsgC12
  , forsPkFromSig   := forsPkFromSigC12
  , wotsPkFromSig   := wotsPkFromSigC12
  , wotsGrindingOk  := wotsGrindingOkC12
  , xmssRootFromSig := xmssRootFromSigC12 }

end C12Concrete
end SphincsMinusVerifierSpec
