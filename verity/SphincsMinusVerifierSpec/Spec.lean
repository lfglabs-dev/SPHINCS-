/-
  Lean 4 specification for the SPHINCS- verifier variants in nconsigny/SPHINCS-.

  This file is intentionally a *specification layer*, not an implementation model.
  Hashes, address serialization, and signature parsing are named semantic
  functions. A Verity proof for a Solidity verifier should show that the EVM
  model refines `verifySpec`: on every non-reverting execution it returns true
  exactly when the abstract reconstruction reaches the public root.
-/

namespace SphincsMinusVerifierSpec

abbrev Bytes := ByteArray

inductive HashAlg where
  | keccak256
  | sha256_MGF1
  deriving DecidableEq, Repr

inductive AddressFormat where
  | fipsUncompressed
  | fipsCompressed
  | jardin
  deriving DecidableEq, Repr

inductive WotsMode where
  | standardChecksum
  | grindingTarget (targetSum : Nat)
  deriving DecidableEq, Repr

inductive ForsMode where
  | standard
  | grindingForcedZero (forcedTree : Nat)
  deriving DecidableEq, Repr

structure Variant where
  name          : String
  n             : Nat
  fullPkSeed    : Bool
  fullPkRoot    : Bool
  h             : Nat
  d             : Nat
  subtreeH      : Nat
  forsK         : Nat
  forsA         : Nat
  forsAuthTrees : Nat
  wotsW         : Nat
  wotsLen       : Nat
  rBytes        : Nat
  sigBytes      : Nat
  hashAlg       : HashAlg
  adrsFormat    : AddressFormat
  wotsMode      : WotsMode
  forsMode      : ForsMode
  deriving Repr

def Variant.paramOk (v : Variant) : Prop :=
  v.h = v.d * v.subtreeH ∧
  v.forsAuthTrees ≤ v.forsK ∧
  (v.rBytes = v.n ∨ v.rBytes = 2 * v.n)

def c13 : Variant :=
  { name := "SPHINCS-C13"
  , n := 16
  , fullPkSeed := true
  , fullPkRoot := true
  , h := 22
  , d := 2
  , subtreeH := 11
  , forsK := 7
  , forsA := 19
  , forsAuthTrees := 6
  , wotsW := 8
  , wotsLen := 43
  , rBytes := 16
  , sigBytes := 3688
  , hashAlg := .keccak256
  , adrsFormat := .fipsUncompressed
  , wotsMode := .grindingTarget 208
  , forsMode := .grindingForcedZero 6 }

def c12 : Variant :=
  { name := "SPHINCS-C12"
  , n := 16
  , fullPkSeed := true
  , fullPkRoot := true
  , h := 20
  , d := 5
  , subtreeH := 4
  , forsK := 20
  , forsA := 7
  , forsAuthTrees := 20
  , wotsW := 8
  , wotsLen := 45
  , rBytes := 32
  , sigBytes := 6512
  , hashAlg := .keccak256
  , adrsFormat := .jardin
  , wotsMode := .standardChecksum
  , forsMode := .standard }

def slhDsaSha2_128_24 : Variant :=
  { name := "SLH-DSA-SHA2-128s-24"
  , n := 16
  , fullPkSeed := false
  , fullPkRoot := false
  , h := 22
  , d := 1
  , subtreeH := 22
  , forsK := 6
  , forsA := 24
  , forsAuthTrees := 6
  , wotsW := 4
  , wotsLen := 68
  , rBytes := 16
  , sigBytes := 3856
  , hashAlg := .sha256_MGF1
  , adrsFormat := .fipsCompressed
  , wotsMode := .standardChecksum
  , forsMode := .standard }

theorem c13_paramOk : c13.paramOk := by
  simp [Variant.paramOk, c13]

theorem c12_paramOk : c12.paramOk := by
  simp [Variant.paramOk, c12]

theorem slhDsaSha2_128_24_paramOk : slhDsaSha2_128_24.paramOk := by
  simp [Variant.paramOk, slhDsaSha2_128_24]

structure PublicKey where
  pkSeed : Bytes
  pkRoot : Bytes

structure HMsg where
  /-- FORS message indices, one per FORS tree. -/
  forsIndex : List Nat
  /-- Bottom-tree leaf index consumed first, then upper layers by division. -/
  leafIndex : Nat
  /-- Hypertree tree index consumed by shifting `subtreeH` bits per layer. -/
  treeIndex : Nat

structure ForsSig where
  sk       : List Bytes
  authPath : List (List Bytes)

structure WotsSig where
  chains : List Bytes
  /-- Present only for WOTS+C variants. Ignored by standard WOTS+. -/
  count  : Nat

structure XmssLayerSig where
  wots     : WotsSig
  authPath : List Bytes

structure Signature where
  R      : Bytes
  fors   : ForsSig
  layers : List XmssLayerSig

/--
Semantic primitives used by the verifier.

The address format and hash algorithm are part of `Variant`; these functions
must interpret them exactly. For example, C13 uses Keccak-256 over
`seed || FIPS-uncompressed-ADRS || payload`, while the SHA2 variant uses the
FIPS compressed ADRS and SHA-256/MGF1 construction.
-/
structure Primitives where
  canonicalPkPart : (fullWord : Bool) → Bytes → Bool
  parseSignature  : (v : Variant) → Bytes → Option Signature
  hMsg            : (v : Variant) → PublicKey → Bytes → Bytes → HMsg
  forsPkFromSig   : (v : Variant) → PublicKey → HMsg → ForsSig → Option Bytes
  wotsPkFromSig   : (v : Variant) → PublicKey → Nat → Nat → Bytes → WotsSig → Option Bytes
  xmssRootFromSig : (v : Variant) → PublicKey → Nat → Nat → Bytes → List Bytes → Option Bytes

def forcedZeroOk (v : Variant) (digest : HMsg) : Bool :=
  match v.forsMode with
  | .standard => true
  | .grindingForcedZero t =>
      t < v.forsK && digest.forsIndex[t]? == some 0

def allSized (n : Nat) (xs : List Bytes) : Bool :=
  xs.all (fun x => x.size == n)

def allAuthSized (height : Nat) (xs : List (List Bytes)) : Bool :=
  xs.all (fun x => x.length == height)

def signatureShapeOk (v : Variant) (sig : Signature) : Bool :=
  sig.R.size == v.rBytes &&
  sig.fors.sk.length == v.forsK &&
  allSized v.n sig.fors.sk &&
  sig.fors.authPath.length == v.forsAuthTrees &&
  allAuthSized v.forsA sig.fors.authPath &&
  sig.layers.length == v.d &&
  sig.layers.all (fun layer =>
    layer.wots.chains.length == v.wotsLen &&
    allSized v.n layer.wots.chains &&
    layer.authPath.length == v.subtreeH &&
    allSized v.n layer.authPath)

def publicKeyOk (p : Primitives) (v : Variant) (pk : PublicKey) : Bool :=
  p.canonicalPkPart v.fullPkSeed pk.pkSeed &&
  p.canonicalPkPart v.fullPkRoot pk.pkRoot

partial def foldHypertreeAux
    (p : Primitives) (v : Variant) (pk : PublicKey)
    (layer : Nat) (treeIdx leafIdx : Nat) (node : Bytes)
    (layers : List XmssLayerSig) : Option Bytes :=
  if layer < v.d then
    match layers[layer]? with
    | none => none
    | some lsig =>
    match p.wotsPkFromSig v pk treeIdx leafIdx node lsig.wots with
    | none => none
    | some wotsPk =>
        match p.xmssRootFromSig v pk treeIdx leafIdx wotsPk lsig.authPath with
        | none => none
        | some root =>
            foldHypertreeAux p v pk (layer + 1)
              (treeIdx / 2 ^ v.subtreeH) (treeIdx % 2 ^ v.subtreeH) root layers
  else
    some node

def foldHypertree
    (p : Primitives) (v : Variant) (pk : PublicKey)
    (digest : HMsg) (startNode : Bytes) (layers : List XmssLayerSig) : Option Bytes :=
  foldHypertreeAux p v pk 0 digest.treeIndex digest.leafIndex startNode layers

/--
Main verifier specification.

For the linked Nico contracts:
* bad signature length is malformed and should correspond to the Solidity revert;
* malformed public keys matter for the SHA2 verifier, where high-16-byte
  canonicality is checked by the contract;
* otherwise verification succeeds iff FORS reconstruction, all WOTS/XMSS
  layers, and final root comparison succeed under the selected variant.
-/
def verifySpec (p : Primitives) (v : Variant)
    (pk : PublicKey) (message sigBytes : Bytes) : Option Bool :=
  if sigBytes.size ≠ v.sigBytes then
    none
  else if ¬ publicKeyOk p v pk then
    none
  else
    match p.parseSignature v sigBytes with
    | none => none
    | some sig =>
        let digest := p.hMsg v pk sig.R message
        if ¬ forcedZeroOk v digest then
          some false
        else if ¬ signatureShapeOk v sig then
          some false
        else
          match p.forsPkFromSig v pk digest sig.fors with
          | none => some false
          | some forsPk =>
              match foldHypertree p v pk digest forsPk sig.layers with
              | none => some false
              | some root => some (root == pk.pkRoot)

/--
Refinement target for a Verity-modeled Solidity verifier. `exec` is the
observable model of `verify(pkSeed, pkRoot, message, sig)`: `none` means revert,
and `some b` means normal return with boolean `b`.
-/
def ImplementsVerifier
    (p : Primitives) (v : Variant)
    (exec : PublicKey → Bytes → Bytes → Option Bool) : Prop :=
  ∀ pk message sig, exec pk message sig = verifySpec p v pk message sig

end SphincsMinusVerifierSpec
