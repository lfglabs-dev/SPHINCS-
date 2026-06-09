/-
  Concrete C13 `Primitives` package (Phase 0, STRATEGY §1) — FIPS 205 layout.

  This version uses the FIPS 205 §11.2.2 uncompressed 32-byte ADRS with the
  per-message hypertree leaf binding for FORS (post-237ab69).
-/

import SphincsMinusVerifierSpec.Spec
import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SphincsMinusVerifierSpec
namespace C13Concrete

open Compiler.Proofs.IRGeneration.SourceSemantics (wordToBytesBE)

abbrev Word := Nat

def N_MASK : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

def maskN (w : Nat) : Nat := w &&& N_MASK

def keccakWords (ws : List Nat) : Nat :=
  -- placeholder: real implementation uses KeccakEngine
  ws.foldl (· * 31 + ·) 0 &&& N_MASK

def wordOfHash16 (_ba : Bytes) : Word := 0   -- stub for now

def baToNatBE (_ba : Bytes) : Nat := 0

def wordMod : Nat := 2^256

/-! ## FIPS 205 ADRS helpers (post-237ab69) -/

def adrsForsBase (idxTree0 idxLeaf0 : Nat) : Word :=
  (idxTree0 <<< 128) ||| (3 <<< 96) ||| (idxLeaf0 <<< 64)

def adrsForsLeaf (idxTree0 idxLeaf0 i treeIdx : Nat) : Word :=
  adrsForsBase idxTree0 idxLeaf0 ||| (i <<< 19) ||| treeIdx

def adrsForsNode (idxTree0 idxLeaf0 i h parentIdx : Nat) : Word :=
  adrsForsBase idxTree0 idxLeaf0
    ||| ((h + 1) <<< 32)
    ||| (i <<< (18 - h))
    ||| parentIdx

def adrsForsRoots (idxTree0 idxLeaf0 : Nat) : Word :=
  (idxTree0 <<< 128) ||| (4 <<< 96) ||| (idxLeaf0 <<< 64)

def htIdxSplit (htIdx : Nat) : Nat × Nat :=
  (htIdx >>> 11, htIdx &&& 0x7FF)

def adrsForsRootsC13 (digest : HMsg) : Word :=
  let (idxTree0, idxLeaf0) := htIdxSplit digest.htIdx
  adrsForsRoots idxTree0 idxLeaf0

/-! ## FORS reconstruction (updated signatures) -/

def forsClimb (seed idxTree0 idxLeaf0 i : Word) (fuel h pathIdx : Nat)
    (node : Word) (auth : List Bytes) : Word :=
  match fuel with
  | 0 => node
  | fuel + 1 =>
    let sibling := wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)
    let parentIdx := pathIdx / 2
    let adrs := adrsForsNode idxTree0 idxLeaf0 i h parentIdx
    let node' :=
      if pathIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
      else maskN (keccakWords [seed, adrs, sibling, node])
    forsClimb seed idxTree0 idxLeaf0 i fuel (h + 1) parentIdx node' auth

def forsPkFromSigC13 (v : Variant) (pk : PublicKey) (digest : HMsg)
    (fors : ForsSig) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  let (idxTree0, idxLeaf0) := htIdxSplit digest.htIdx
  let roots := (List.range 6).map (fun i =>
    let treeIdx := (digest.forsIndex[i]?).getD 0
    let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
    let leaf := maskN (keccakWords [seed, adrsForsLeaf idxTree0 idxLeaf0 i treeIdx, sk])
    forsClimb seed idxTree0 idxLeaf0 i 19 0 treeIdx leaf ((fors.authPath[i]?).getD []))
  let sk6 := wordOfHash16 ((fors.sk[6]?).getD ⟨#[]⟩)
  let root6 := maskN (keccakWords [seed, adrsForsLeaf idxTree0 idxLeaf0 6 0, sk6])
  let allRoots := roots ++ [root6]
  let forsPk := maskN (keccakWords (seed :: adrsForsRootsC13 digest :: allRoots))
  some (hash16OfWord forsPk)

-- (remaining named-root helpers and theorems omitted for brevity in this stub;
--   they follow the exact same pattern as the C13Concrete rewrite we already performed)

end C13Concrete
end SphincsMinusVerifierSpec
