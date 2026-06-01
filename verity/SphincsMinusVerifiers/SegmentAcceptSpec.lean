/-
  SegmentAcceptSpec — the compose-stub mandated by STRATEGY (§2, "Worker E stubs
  the compose early to catch drift").

  `SegmentCompose.execC13Body_returns` already reduces the *entire* `c13VerifyBody`
  run, under the three control-flow guards, to a single `.return` whose payload is
  the EVM boolean word of the model's final `currentNode == root` comparison
  (`acceptWord st`).  That closes the **control-flow** side end-to-end.

  This file ties that returned boolean to the **spec** side: `verifyParsed`'s
  accept decision.  It does so under ONE explicit hypothesis, `hCmp`, which states
  that the model's final node/root word comparison agrees with the boolean
  `verifyParsed` returns.  `hCmp` is precisely the residual Phase-3b
  data-correspondence obligation (the months-scale FORS double-loop + hypertree
  keccak matching), surfaced here as a named hypothesis rather than discharged.

  The value of this stub is drift-detection: it is phrased against the REAL
  `verifyParsed`, `c13PrimitivesConcrete`, `c13`, `mkC13State`, and `c13VerifyBody`
  definitions, so any change to the model's return structure or the spec's accept
  shape breaks compilation here.  It touches neither `execC13` nor the bridge
  axiom, and discharges no data correspondence.  No `sorry`, no new `axiom`,
  no `native_decide`.
-/

import SphincsMinusVerifiers.SegmentCompose
import SphincsMinusVerifiers.SegmentS2R
import SphincsMinusVerifiers.MkC13State
import SphincsMinusVerifiers.RootFrame
import SphincsMinusVerifiers.CurrentNodeFrame
import SphincsMinusVerifierSpec.Spec
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentAcceptSpec

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.RootFrame
open SphincsMinusVerifiers.CurrentNodeFrame
open SphincsMinusVerifierSpec
open SphincsMinusVerifierSpec.C13Concrete

/-! ## Residual `hCmp` factoring. -/

/-- When the parsed verifier reaches the final `.ok root` branch, its observable
boolean is exactly `root == pk.pkRoot`.  This is the spec-side branch equation
needed by the model-side final-word comparison. -/
theorem verifyParsed_ok_branch
    (p : Primitives) (v : Variant)
    (pk : PublicKey) (message : ByteArray) (sigParsed : Signature)
    (forsPk root : ByteArray)
    (hShape : signatureShapeOk v sigParsed = true)
    (hZero : forcedZeroOk v (p.hMsg v pk sigParsed.R message) = true)
    (hFors : p.forsPkFromSig v pk (p.hMsg v pk sigParsed.R message) sigParsed.fors
              = some forsPk)
    (hFold : foldHypertree p v pk (p.hMsg v pk sigParsed.R message) forsPk sigParsed.layers
              = .ok root) :
    verifyParsed p v pk message sigParsed = some (root == pk.pkRoot) := by
  unfold verifyParsed
  simp [hShape, hZero, hFors, hFold]

/-- **`accept_path_returns_verifyParsed_bool`** — under the three control-flow
guards (length, FORS forced-zero, WOTS-checksum climb) AND the single residual
data-correspondence hypothesis `hCmp` (the model's final `currentNode == root`
word comparison decides the same boolean `verifyParsed` returns on this input),
the whole compiled `c13VerifyBody` run over `mkC13State …` returns the EVM-word
encoding of exactly the boolean `verifyParsed` yields.

This is the Phase-3 *compose stub*: it pins the model's observable return to the
spec's accept decision, catching any drift between the two.  It does NOT discharge
`hCmp` — that is the months-scale FORS/hypertree keccak correspondence — and it
neither defines `execC13` nor flips the bridge axiom.  Axiom-clean
(`[propext, Classical.choice, Quot.sound]`). -/
theorem accept_path_returns_verifyParsed_bool
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (specBool : Bool)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hSpec : verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
              = some specBool)
    (hCmp : decide
        (lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
          = lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root")
        = specBool) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed = some specBool ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord specBool)) finalState := by
  obtain ⟨fs, hfs⟩ := execC13Body_returns (mkC13State pkSeed pkRoot message sig) hlen hg3 hgL
  have hAcc : acceptWord (mkC13State pkSeed pkRoot message sig) = boolWord specBool := by
    unfold acceptWord; rw [hCmp]
  refine ⟨fs, hSpec, ?_⟩
  rw [hfs, hAcc]

/-- **`accept_path_returns_verifyParsed_bool_linked`** — the same compose stub as
`accept_path_returns_verifyParsed_bool`, but with the spec-side inputs *pinned to
the byte inputs* via two linkage hypotheses:

* `hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot }` — the public key is exactly
  what `ByteLevel.parsePublicKey`/`verifyBytes` reconstructs from the two `bytes32`
  arguments (Spec.lean:347–350).
* `hSig : parseSignatureC13 c13 sig = some sigParsed` — the parsed signature is
  exactly what `c13PrimitivesConcrete.parseSignature` yields on the raw bytes.

With these, `specBool` (constrained by `hSpec` over `pk`/`sigParsed`) becomes a
*function of the byte inputs alone*, the same bytes the model's
`currentNode`/`root` bindings are computed from.  This makes the residual
data-correspondence goal `decide (currentNode = root) = specBool` **well-posed**
(both sides range over the same `pkSeed pkRoot message sig`), closing *Blocker A*
(the floating-`pk`/`sigParsed` ill-posedness).  It still carries `hCmp` and does
not discharge the keccak correspondence (*Blocker B*).  Axiom-clean. -/
theorem accept_path_returns_verifyParsed_bool_linked
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (specBool : Bool)
    (_hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (_hSig : parseSignatureC13 c13 sig = some sigParsed)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hSpec : verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
              = some specBool)
    (hCmp : decide
        (lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
          = lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root")
        = specBool) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed = some specBool ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord specBool)) finalState := by
  -- The linkage hypotheses pin the spec inputs to the bytes (Blocker A); the proof
  -- itself is the same as the unlinked stub.
  exact accept_path_returns_verifyParsed_bool
    pkSeed pkRoot message sig pk sigParsed specBool hlen hg3 hgL hSpec hCmp

/-- **`accept_path_returns_verifyParsed_bool_from_root`** — a sharper compose
adapter for the residual `hCmp`: if the left operand of the final model compare is
the word image of the spec's final root, and byte equality at the spec boundary is
represented by the corresponding word equality, then the existing accept-path
composition returns the `verifyParsed` boolean.

The right operand is no longer a hypothesis here: it is supplied by
`RootFrame.afterLayer_root_mkC13State`, which proves the final `"root"` binding is
`wordOfHash16 pkRoot`.  The only remaining substantive obligations are therefore:

* `hCurrent`: the post-layer `"currentNode"` binding equals `wordOfHash16 specRoot`;
* `hWordCmp`: the word-level equality test agrees with the spec byte equality.

This is the bounded form of `hCmp` that the FORS/hypertree correspondence should
eventually discharge.  It still does not touch `execC13` or the bridge axiom. -/
theorem accept_path_returns_verifyParsed_bool_from_root
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hCurrent :
        lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
          = wordOfHash16 specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  subst hPk
  have hSpec : verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (specRoot == pkRoot) :=
    verifyParsed_ok_branch C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed forsPk specRoot
      hShape hZero hFors hFold
  have hRoot :
      lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root"
        = wordOfHash16 pkRoot :=
    afterLayer_root_mkC13State pkSeed pkRoot message sig
  have hCmp : decide
      (lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
        = lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root")
      = (specRoot == pkRoot) := by
    rw [hCurrent, hRoot, hWordCmp]
  exact accept_path_returns_verifyParsed_bool
    pkSeed pkRoot message sig { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed
    (specRoot == pkRoot) hlen hg3 hgL hSpec hCmp

/-- A compact way to discharge the final `hWordCmp` premise: if the word encoding
is injective for the two byte roots in question, then the model's word equality
decision agrees with the spec's `ByteArray` equality test. -/
theorem wordCmp_of_wordOfHash16_iff
    (specRoot pkRoot : ByteArray)
    (hIff : (wordOfHash16 specRoot = wordOfHash16 pkRoot) ↔ specRoot = pkRoot)
    (hBeq : (specRoot == pkRoot) = decide (specRoot = pkRoot)) :
    decide (wordOfHash16 specRoot = wordOfHash16 pkRoot) = (specRoot == pkRoot) := by
  rw [hBeq]
  by_cases hWord : wordOfHash16 specRoot = wordOfHash16 pkRoot
  · have hBytes : specRoot = pkRoot := hIff.mp hWord
    simp [hBytes]
  · have hBytes : specRoot ≠ pkRoot := by
      intro hEq
      exact hWord (hIff.mpr hEq)
    simp [hWord, hBytes]

/-- `ByteArray`'s derived `BEq` agrees with propositional equality on canonical
`hash16OfWord` outputs.  This avoids assuming a global `LawfulBEq ByteArray`
instance, which is not available in this environment. -/
theorem hash16OfWord_beq_eq_decide (w1 w2 : Word) :
    (hash16OfWord w1 == hash16OfWord w2)
      = decide (hash16OfWord w1 = hash16OfWord w2) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp [hash16OfWord] at h ⊢
    change
      (((List.map (fun i => UInt8.ofNat (w1 / 256 ^ (31 - i) % 256))
            (List.range 16)).toArray) ==
        ((List.map (fun i => UInt8.ofNat (w2 / 256 ^ (31 - i) % 256))
            (List.range 16)).toArray)) = true at h
    rw [beq_iff_eq] at h
    simpa using h
  · intro h
    simp [hash16OfWord] at h ⊢
    change
      (((List.map (fun i => UInt8.ofNat (w1 / 256 ^ (31 - i) % 256))
            (List.range 16)).toArray) ==
        ((List.map (fun i => UInt8.ofNat (w2 / 256 ^ (31 - i) % 256))
            (List.range 16)).toArray)) = true
    rw [beq_iff_eq]
    simpa using h

/-- If both byte roots are canonical roundtrips through `wordOfHash16` and
`hash16OfWord`, their `ByteArray` equality test agrees with propositional
equality. -/
theorem byteRoot_beq_eq_decide_of_wordOfHash16_roundtrip
    (specRoot pkRoot : ByteArray)
    (hSpec : hash16OfWord (wordOfHash16 specRoot) = specRoot)
    (hPk : hash16OfWord (wordOfHash16 pkRoot) = pkRoot) :
    (specRoot == pkRoot) = decide (specRoot = pkRoot) := by
  rw [← hSpec, ← hPk]
  exact hash16OfWord_beq_eq_decide (wordOfHash16 specRoot) (wordOfHash16 pkRoot)

/-- Canonical root roundtrips are enough to discharge the final word-comparison
premise: word equality is reflected by `hash16OfWord`, and the byte-side `BEq`
is reduced to canonical `hash16OfWord` outputs. -/
theorem wordCmp_of_wordOfHash16_roundtrip
    (specRoot pkRoot : ByteArray)
    (hSpec : hash16OfWord (wordOfHash16 specRoot) = specRoot)
    (hPk : hash16OfWord (wordOfHash16 pkRoot) = pkRoot) :
    decide (wordOfHash16 specRoot = wordOfHash16 pkRoot) = (specRoot == pkRoot) := by
  have hIff :
      (wordOfHash16 specRoot = wordOfHash16 pkRoot) ↔ specRoot = pkRoot := by
    constructor
    · intro hWord
      rw [← hSpec, ← hPk, hWord]
    · intro hBytes
      rw [hBytes]
  exact wordCmp_of_wordOfHash16_iff specRoot pkRoot hIff
    (byteRoot_beq_eq_decide_of_wordOfHash16_roundtrip specRoot pkRoot hSpec hPk)

/-- `UInt8.ofNat` stores the low byte of its natural argument. -/
theorem uint8_toNat_ofNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := rfl

/-- Appending one low base-256 digit to a truncated quotient recovers one more
base-256 digit of `x`. -/
theorem base256_digit_append (x n : Nat) :
    ((x / 256) % 256 ^ n) * 256 + x % 256 = x % 256 ^ (n + 1) := by
  let M := 256 ^ n
  have hpow : 256 ^ (n + 1) = 256 * M := by
    simp [M, pow_succ]
    ring
  rw [hpow]
  calc
    ((x / 256) % M) * 256 + x % 256
        = 256 * ((x / 256) % M) + x % 256 := by ring
    _ = 256 * ((x % (256 * M)) / 256) + (x % (256 * M)) % 256 := by
        rw [Nat.mod_mul_right_div_self]
        have hmod : (x % (256 * M)) % 256 = x % 256 := by
          rw [Nat.mul_comm 256 M]
          exact Nat.mod_mul_left_mod x M 256
        rw [hmod]
    _ = x % (256 * M) := by
        rw [Nat.div_add_mod]

/-- Extract one byte digit from a base-256 decomposition with a bounded tail. -/
theorem base256_digit_decomp
    (a d t s : Nat) (hd : d < 256) (ht : t < 256 ^ s) :
    ((a * 256 ^ (s + 1) + d * 256 ^ s + t) / 256 ^ s) % 256 = d := by
  let m := 256 ^ s
  have hm : 0 < m := Nat.pow_pos (by norm_num : 0 < 256)
  have hpow : 256 ^ (s + 1) = 256 * m := by
    simp [m, pow_succ]
    ring
  have hshape :
      a * 256 ^ (s + 1) + d * 256 ^ s + t
        = (a * 256 + d) * m + t := by
    rw [hpow]
    simp [m]
    ring
  rw [hshape]
  change (((a * 256 + d) * m + t) / m) % 256 = d
  rw [Nat.mul_comm (a * 256 + d) m]
  rw [Nat.mul_add_div hm, Nat.div_eq_of_lt ht, Nat.add_zero]
  rw [Nat.add_comm (a * 256) d]
  rw [Nat.mul_comm a 256]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hd

/-- Pull an initial accumulator out of a big-endian fold over byte values. -/
theorem base256_uint8_fold_init (l : List UInt8) (init : Nat) :
    l.foldl (fun acc b => acc * 256 + b.toNat) init
      = init * 256 ^ l.length + l.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons b bs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (init * 256 + b.toNat), ih (0 * 256 + b.toNat)]
      ring

/-- A big-endian fold over bytes is bounded by the corresponding base-256
width. -/
theorem base256_uint8_fold_lt (l : List UInt8) :
    l.foldl (fun acc b => acc * 256 + b.toNat) 0 < 256 ^ l.length := by
  have h :
      ∀ (l : List UInt8) (init k : Nat), init < 256 ^ k →
        l.foldl (fun acc b => acc * 256 + b.toNat) init < 256 ^ (k + l.length) := by
    intro l
    induction l with
    | nil =>
        intro init k hinit
        simpa using hinit
    | cons b bs ih =>
        intro init k hinit
        simp only [List.foldl_cons, List.length_cons]
        have hnew : init * 256 + b.toNat < 256 ^ (k + 1) := by
          have hb : b.toNat < 256 := b.toNat_lt_size
          have hpow : 256 ^ (k + 1) = 256 ^ k * 256 := by rw [pow_succ]
          omega
        have hrec := ih (init * 256 + b.toNat) (k + 1) hnew
        have hExp : k + 1 + bs.length = k + (bs.length + 1) := by omega
        rwa [hExp] at hrec
  simpa using h l 0 0 (by norm_num)

/-- The `i`th byte of a fixed base-256 fold can be selected by shifting away the
lower bytes and reducing modulo 256. -/
theorem base256_fold_digit_of_list
    (l : List UInt8) (i : Nat) (hi : i < l.length) :
    (l.foldl (fun acc b => acc * 256 + b.toNat) 0 /
        256 ^ (l.length - 1 - i)) % 256 = l[i].toNat := by
  let tail := l.drop (i + 1)
  have hsplit : l = l.take i ++ l[i] :: tail := by
    rw [← List.drop_eq_getElem_cons hi]
    exact (List.take_append_drop i l).symm
  have htailLen : tail.length = l.length - (i + 1) := by
    simp [tail]
  have hExp : l.length - 1 - i = tail.length := by
    rw [htailLen]
    omega
  have htailLt :
      tail.foldl (fun acc b => acc * 256 + b.toNat) 0 < 256 ^ tail.length :=
    base256_uint8_fold_lt tail
  have hfold :
      l.foldl (fun acc b => acc * 256 + b.toNat) 0 =
        (l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0 *
            256 ^ (tail.length + 1) +
          l[i].toNat * 256 ^ tail.length +
          tail.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
    calc
      l.foldl (fun acc b => acc * 256 + b.toNat) 0
          = (l.take i ++ l[i] :: tail).foldl
              (fun acc b => acc * 256 + b.toNat) 0 := by
            exact congrArg (fun xs => xs.foldl (fun acc b => acc * 256 + b.toNat) 0) hsplit
      _ = (l[i] :: tail).foldl
              (fun acc b => acc * 256 + b.toNat)
              ((l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0) := by
            rw [List.foldl_append]
      _ = (l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0 *
              256 ^ (tail.length + 1) +
            (l[i] :: tail).foldl (fun acc b => acc * 256 + b.toNat) 0 := by
            rw [base256_uint8_fold_init (l[i] :: tail)]
            simp
      _ = (l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0 *
              256 ^ (tail.length + 1) +
            l[i].toNat * 256 ^ tail.length +
            tail.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
            simp only [List.foldl_cons, zero_mul, zero_add]
            rw [base256_uint8_fold_init tail l[i].toNat]
            ring
  rw [hfold, hExp]
  exact base256_digit_decomp
    ((l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0)
    l[i].toNat
    (tail.foldl (fun acc b => acc * 256 + b.toNat) 0)
    tail.length
    l[i].toNat_lt_size htailLt

/-- `baToNatBE` is the big-endian fold of the backing byte list. -/
theorem baToNatBE_eq_data_toList (b : ByteArray) :
    baToNatBE b =
      b.data.toList.foldl (fun acc byte => acc * 256 + byte.toNat) 0 := by
  unfold baToNatBE
  rw [SegmentS2R.ba_foldl_eq]
  conv_lhs => rw [← Array.toArray_toList (xs := b.data)]
  rw [List.foldl_toArray' (fun acc byte => acc * 256 + byte.toNat) 0 b.data.toList rfl]

/-- A byte array of size 16 folds to a 128-bit natural. -/
theorem baToNatBE_lt_of_size (b : ByteArray) (hsize : b.size = 16) :
    baToNatBE b < 2 ^ 128 := by
  rw [baToNatBE_eq_data_toList]
  have h := base256_uint8_fold_lt b.data.toList
  have hpow : (256 : Nat) ^ b.data.toList.length = 2 ^ 128 := by
    have hlen : b.data.toList.length = 16 := by
      simpa [ByteArray.size, Array.length_toList] using hsize
    rw [hlen]
    norm_num
  rwa [hpow] at h

/-- A 16-byte array is already canonical for the C13
`hash16OfWord`/`wordOfHash16` byte roundtrip. -/
theorem hash16OfWord_wordOfHash16_of_size
    (b : ByteArray) (hsize : b.size = 16) :
    hash16OfWord (wordOfHash16 b) = b := by
  apply ByteArray.ext
  apply Array.ext
  · simpa [hash16OfWord, ByteArray.size] using hsize.symm
  · intro i hiHash hiB
    apply UInt8.toNat_inj.mp
    have hi : i < 16 := by
      simpa [hash16OfWord, List.size_toArray] using hiHash
    have hbaLt : baToNatBE b < 2 ^ 128 := baToNatBE_lt_of_size b hsize
    have hpow128 : (2 : Nat) ^ 128 = 256 ^ 16 := by norm_num
    have hbaLt256 : baToNatBE b < 256 ^ 16 := by
      rwa [← hpow128]
    have hExp : 31 - i = 16 + (15 - i) := by omega
    have hDigit :
        (b.data.toList.foldl (fun acc byte => acc * 256 + byte.toNat) 0 /
            256 ^ (15 - i)) % 256 = b.data[i].toNat := by
      have hListIdx : i < b.data.toList.length := by
        simpa [Array.length_toList] using hiB
      have hLen : b.data.toList.length = 16 := by
        simpa [ByteArray.size, Array.length_toList] using hsize
      have hbase := base256_fold_digit_of_list b.data.toList i hListIdx
      have hExpList : b.data.toList.length - 1 - i = 15 - i := by
        rw [hLen]
      have hGet : b.data.toList[i] = b.data[i] := by
        exact Array.getElem_toList (xs := b.data) hiB
      rw [hExpList] at hbase
      rw [hGet] at hbase
      exact hbase
    simp [hash16OfWord, wordOfHash16]
    change
      (baToNatBE b % 2 ^ 128 * 2 ^ 128 / 256 ^ (31 - i) % 256
        = b.data[i].toNat)
    rw [hpow128, Nat.mod_eq_of_lt hbaLt256, hExp]
    rw [Nat.pow_add]
    rw [Nat.mul_comm (baToNatBE b) (256 ^ 16)]
    rw [Nat.mul_div_mul_left _ _ (Nat.pow_pos (by norm_num : 0 < 256))]
    rw [baToNatBE_eq_data_toList]
    exact hDigit

/-- Folding `n` high-to-low base-256 digits of `w`, starting at byte offset `k`,
is the corresponding `n`-byte window of `w`. -/
theorem highDigitsFold_eq_mod (w k n : Nat) :
    (List.range n).foldl
      (fun acc i => acc * 256 + w / 256 ^ (k + n - 1 - i) % 256) 0
      = (w / 256 ^ k) % 256 ^ n := by
  induction n generalizing k with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      have hfun :
          (fun acc i => acc * 256 + w / 256 ^ (k + (n + 1) - 1 - i) % 256)
          = (fun acc i => acc * 256 + w / 256 ^ (k + 1 + n - 1 - i) % 256) := by
        funext acc i
        have : k + (n + 1) - 1 - i = k + 1 + n - 1 - i := by omega
        rw [this]
      rw [hfun, ih (k + 1)]
      simp only [List.foldl_cons, List.foldl_nil]
      have hlast : k + 1 + n - 1 - n = k := by omega
      rw [hlast]
      have hdiv : w / 256 ^ (k + 1) = (w / 256 ^ k) / 256 := by
        rw [Nat.div_div_eq_div_mul]
        congr 1
      rw [hdiv]
      exact base256_digit_append (w / 256 ^ k) n

/-- A low byte selected from the high half after truncating to 16 bytes is the
same byte selected from the original word. -/
theorem highHalf_mod_digit (w r : Nat) (hr : r < 16) :
    (((w / 256 ^ 16) % 256 ^ 16) * 256 ^ 16) / 256 ^ (16 + r) % 256
      = w / 256 ^ (16 + r) % 256 := by
  set x := w / 256 ^ 16
  have hpowDen : 256 ^ (16 + r) = 256 ^ 16 * 256 ^ r := by
    rw [Nat.pow_add]
  have hright : w / 256 ^ (16 + r) = x / 256 ^ r := by
    rw [hpowDen, ← Nat.div_div_eq_div_mul]
  rw [hright, hpowDen]
  have hdivmul :
      (x % 256 ^ 16 * 256 ^ 16) / (256 ^ 16 * 256 ^ r)
        = (x % 256 ^ 16) / 256 ^ r := by
    rw [Nat.mul_comm (256 ^ 16) (256 ^ r)]
    exact Nat.mul_div_mul_right (x % 256 ^ 16) (256 ^ r)
      (Nat.pow_pos (by norm_num : 0 < 256))
  rw [hdivmul]
  have hpow16 : 256 ^ 16 = 256 ^ r * 256 ^ (16 - r) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hpow16, Nat.mod_mul_right_div_self]
  have hdvd : 256 ∣ 256 ^ (16 - r) := by
    refine ⟨256 ^ (15 - r), ?_⟩
    rw [show 16 - r = (15 - r) + 1 by omega, pow_succ]
    ring
  exact Nat.mod_mod_of_dvd (x / 256 ^ r) hdvd

/-- Canonical `hash16OfWord` outputs roundtrip through `wordOfHash16`. -/
theorem hash16OfWord_wordOfHash16_hash16OfWord (w : Word) :
    hash16OfWord (wordOfHash16 (hash16OfWord w)) = hash16OfWord w := by
  simp [hash16OfWord, wordOfHash16, SegmentS2R.baToNatBE_toArray]
  intro a ha
  rw [List.foldl_map]
  simp only [uint8_toNat_ofNat, Nat.mod_mod]
  have hfold :
      (List.foldl
          (fun acc i => acc * 256 + w / 256 ^ (31 - i) % 256) 0
          (List.range 16)) = (w / 256 ^ 16) % 256 ^ 16 := by
    convert highDigitsFold_eq_mod w 16 16 using 2
  rw [hfold]
  change
    UInt8.ofNat
      (((w / 256 ^ 16 % 256 ^ 16 % 256 ^ 16) * 256 ^ 16
          / 256 ^ (31 - a)) % 256)
      = UInt8.ofNat (w / 256 ^ (31 - a) % 256)
  rw [Nat.mod_mod]
  congr 1
  have hr : 15 - a < 16 := by omega
  have hExp : 31 - a = 16 + (15 - a) := by omega
  rw [hExp]
  exact highHalf_mod_digit w (15 - a) hr

/-- Reading the high 16 bytes of a word as a `ByteArray` and folding them back
big-endian recovers the word's high 128-bit window. -/
theorem baToNatBE_hash16OfWord (w : Word) :
    baToNatBE (hash16OfWord w) = (w / 256 ^ 16) % 256 ^ 16 := by
  simp [hash16OfWord, SegmentS2R.baToNatBE_toArray]
  rw [List.foldl_map]
  simp only [uint8_toNat_ofNat, Nat.mod_mod]
  convert highDigitsFold_eq_mod w 16 16 using 1

/-- A word already shaped as a high-half C13 hash roundtrips through
`hash16OfWord` and `wordOfHash16`. -/
theorem wordOfHash16_hash16OfWord_highHalf
    (h : Nat) (hh : h < 2 ^ 128) :
    wordOfHash16 (hash16OfWord (h * 2 ^ 128)) = h * 2 ^ 128 := by
  unfold wordOfHash16
  rw [baToNatBE_hash16OfWord]
  have hpow : (256 : Nat) ^ 16 = 2 ^ 128 := by norm_num
  rw [hpow]
  have hdiv : h * 2 ^ 128 / 2 ^ 128 = h := by
    exact Nat.mul_div_left h (Nat.pow_pos (by norm_num : 0 < 2))
  rw [hdiv]
  rw [Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hh]

/-- A bounded 256-bit word masked by C13's `N_MASK` is already canonical for
the `hash16OfWord`/`wordOfHash16` conversion. -/
theorem wordOfHash16_hash16OfWord_maskN_of_lt
    (w : Word) (hw : w < 2 ^ 256) :
    wordOfHash16 (hash16OfWord (maskN w)) = maskN w := by
  let hi := w / 2 ^ 128
  let lo := w % 2 ^ 128
  have hpow : 2 ^ 256 = 2 ^ 128 * 2 ^ 128 := by norm_num
  have hhi : hi < 2 ^ 128 := by
    unfold hi
    exact Nat.div_lt_of_lt_mul (by
      show w < 2 ^ 128 * 2 ^ 128
      rwa [← hpow])
  have hlo : lo < 2 ^ 128 := by
    unfold lo
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num : 0 < 2))
  have hsplit : w = hi * 2 ^ 128 + lo := by
    unfold hi lo
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod w (2 ^ 128)).symm
  have hmask : maskN w = hi * 2 ^ 128 := by
    unfold maskN
    rw [hsplit]
    rw [show nMask = SphincsMinusVerifiers.ClimbKit.N_MASK from rfl]
    exact SegmentS2R.land_nmask hi lo hhi hlo
  rw [hmask]
  exact wordOfHash16_hash16OfWord_highHalf hi hhi

/-- The named C13 FORS public-key compression word is masked, hence canonical
for the `hash16OfWord`/`wordOfHash16` conversion. -/
theorem forsPkWordC13_roundtrip
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    wordOfHash16 (hash16OfWord (C13Concrete.forsPkWordC13 pk digest fors))
      = C13Concrete.forsPkWordC13 pk digest fors := by
  let seed := wordOfHash16 pk.pkSeed
  let words := seed :: C13Concrete.adrsForsRoots ::
    C13Concrete.forsAllRootsC13 pk digest fors
  have hlt : C13Concrete.keccakWords words < 2 ^ 256 := by
    simpa [Compiler.Constants.evmModulus] using
      SphincsMinusVerifiers.KeccakBridge.keccakWords_lt words
  simpa [C13Concrete.forsPkWordC13, words, seed] using
    wordOfHash16_hash16OfWord_maskN_of_lt (C13Concrete.keccakWords words) hlt

/-- Any byte string known to be a canonical C13 `hash16OfWord` output roundtrips
through `wordOfHash16`. -/
theorem hash16OfWord_wordOfHash16_of_canonical
    (b : ByteArray) (h : C13Concrete.CanonicalHash16 b) :
    hash16OfWord (wordOfHash16 b) = b := by
  rcases h with ⟨w, rfl⟩
  exact hash16OfWord_wordOfHash16_hash16OfWord w

/-- A successful C13 FORS reconstruction followed by a successful C13 hypertree
fold produces a root that roundtrips through `wordOfHash16`/`hash16OfWord`. -/
theorem specRoot_roundtrip_of_c13_fors_fold
    {pk : PublicKey} {digest : HMsg} {fors : ForsSig} {forsPk specRoot : ByteArray}
    {layers : List XmssLayerSig}
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk digest fors
        = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk digest forsPk layers
        = .ok specRoot) :
    hash16OfWord (wordOfHash16 specRoot) = specRoot :=
  hash16OfWord_wordOfHash16_of_canonical specRoot
    (C13Concrete.foldHypertree_c13_ok_root_canonical_of_fors hFors hFold)

/-- **Layer-step form of the final accept adapter.**  This replaces the raw
`hCurrent` hypothesis of `accept_path_returns_verifyParsed_bool_from_root` with
the two facts the hypertree proof is expected to produce:

* S4/FORS finalize binds `"forsPk"` to the word image of the spec FORS public key;
* one `stepLayer` iteration preserves the `"currentNode"` ↔ spec-node relation,
  so `CurrentNodeFrame.afterLayer_currentNode_wordOfHash16_of_forsPk_step` lifts it
  across the two-layer C13 loop.

The per-layer correspondence is still a hypothesis here; this theorem only
performs the segment composition from that correspondence to the final
`verifyParsed` boolean. -/
theorem accept_path_returns_verifyParsed_bool_from_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hForsPkWord :
        lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings "forsPk"
          = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  have hCurrent :
      lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
        = wordOfHash16 specRoot :=
    CurrentNodeFrame.afterLayer_currentNode_wordOfHash16_of_forsPk_step
      (mkC13State pkSeed pkRoot message sig) specStep forsPk specRoot
      hForsPkWord hLayerStep hSpecFold
  exact accept_path_returns_verifyParsed_bool_from_root
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot hPk hShape hZero hFors hFold
    hlen hg3 hgL hCurrent hWordCmp

/-- Same as `accept_path_returns_verifyParsed_bool_from_layer_step`, but the S4
premise is the concrete masked FORS-compression word rather than the already-bound
`"forsPk"` lookup.  This is the handoff shape for the forthcoming S4/FORS root
correspondence proof. -/
theorem accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hForsCompress :
        CurrentNodeFrame.forsPkCompressWord
          (afterFors (mkC13State pkSeed pkRoot message sig)) = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  have hForsPkWord :
      lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings "forsPk"
        = wordOfHash16 forsPk :=
    CurrentNodeFrame.afterFinalize_forsPk_of_compress
      (mkC13State pkSeed pkRoot message sig) forsPk hForsCompress
  exact accept_path_returns_verifyParsed_bool_from_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep hPk
    hShape hZero hFors hFold hlen hg3 hgL hForsPkWord hLayerStep hSpecFold hWordCmp

/-- Range-gated S4/FORS-root form of the final accept adapter.  It replaces the
raw `hForsCompress` premise with the concrete frozen-entry compression frame:
the seed cell is preserved across the real `i < 6` FORS loop, six root cells plus
the forced-root cell are supplied from the pre-copy frame, and a spec-side
compression equality identifies those seven roots with `forsPk`. -/
theorem accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (roots : List Nat)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hRootsLen : roots.length = 7)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega))
    (hForsPkCompress :
        C13Concrete.maskN
          (C13Concrete.keccakWords
            (C13Concrete.wordOfHash16 pkSeed :: C13Concrete.adrsForsRoots :: roots))
          = C13Concrete.wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  have hForsCompress :
      CurrentNodeFrame.forsPkCompressWord
        (afterFors (mkC13State pkSeed pkRoot message sig)) = wordOfHash16 forsPk := by
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last_range
      pkSeed pkRoot message sig roots hRootsLen hLeaf hmRlo hmRlast]
    exact hForsPkCompress
  exact accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep hPk
    hShape hZero hFors hFold hlen hg3 hgL hForsCompress hLayerStep hSpecFold hWordCmp

/-- Seed-cell form of the final accept adapter.  Compared with
`accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range`,
this takes the exact seed cell needed by FORS public-key compression directly,
instead of a quantified `forsLeafStep` preservation premise. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_and_fors_roots_and_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (roots : List Nat)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hRootsLen : roots.length = 7)
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega))
    (hForsPkCompress :
        C13Concrete.maskN
          (C13Concrete.keccakWords
            (C13Concrete.wordOfHash16 pkSeed :: C13Concrete.adrsForsRoots :: roots))
          = C13Concrete.wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  have hForsCompress :
      CurrentNodeFrame.forsPkCompressWord
        (afterFors (mkC13State pkSeed pkRoot message sig)) = wordOfHash16 forsPk := by
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_seed_mkC13State_six_plus_last
      pkSeed pkRoot message sig roots hRootsLen hmSeed hmRlo hmRlast]
    exact hForsPkCompress
  exact accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep hPk
    hShape hZero hFors hFold hlen hg3 hgL hForsCompress hLayerStep hSpecFold hWordCmp

/-- Named-root-list form of
`accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range`.
The seven S4 root cells are stated directly against
`C13Concrete.forsAllRootsC13`, and the compression premise is the named
`C13Concrete.forsPkWordC13` word. -/
theorem accept_path_returns_verifyParsed_bool_from_named_fors_roots_and_layer_step_range
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkWord :
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkCompress :
      C13Concrete.maskN
        (C13Concrete.keccakWords
          (C13Concrete.wordOfHash16 pkSeed :: C13Concrete.adrsForsRoots ::
            C13Concrete.forsAllRootsC13 pk digest sigParsed.fors))
        = C13Concrete.wordOfHash16 forsPk := by
    subst hPk
    simpa [digest, C13Concrete.forsPkWordC13] using hForsPkWord
  exact accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
    hPk hShape hZero hFors hFold hlen hg3 hgL
    (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors)
    hLeaf
    (by
      intro j hj
      simpa [digest] using hmRlo j hj)
    (by
      simpa [digest] using hmRlast)
    hForsPkCompress hLayerStep hSpecFold hWordCmp

/-- Named-root-list plus direct seed-cell form of the final accept adapter.  This
is the named-root analogue of
`accept_path_returns_verifyParsed_bool_from_seed_and_fors_roots_and_layer_step`:
the root cells are stated against `C13Concrete.forsAllRootsC13`, while the seed
cell is supplied directly at `afterFors`. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_and_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkWord :
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkCompress :
      C13Concrete.maskN
        (C13Concrete.keccakWords
          (C13Concrete.wordOfHash16 pkSeed :: C13Concrete.adrsForsRoots ::
            C13Concrete.forsAllRootsC13 pk digest sigParsed.fors))
        = C13Concrete.wordOfHash16 forsPk := by
    subst hPk
    simpa [digest, C13Concrete.forsPkWordC13] using hForsPkWord
  exact accept_path_returns_verifyParsed_bool_from_seed_and_fors_roots_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
    hPk hShape hZero hFors hFold hlen hg3 hgL
    (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors)
    hmSeed
    (by
      intro j hj
      simpa [digest] using hmRlo j hj)
    (by
      simpa [digest] using hmRlast)
    hForsPkCompress hLayerStep hSpecFold hWordCmp

/-- Same named-root accept adapter as
`accept_path_returns_verifyParsed_bool_from_named_fors_roots_and_layer_step_range`,
but the caller supplies only the canonicality/roundtrip fact for the named
masked FORS compression word.  The byte result equality is derived from `hFors`
and `C13Concrete.forsPkFromSigC13_some_eq_hash16_named`. -/
theorem accept_path_returns_verifyParsed_bool_from_named_fors_roots_roundtrip_and_layer_step_range
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkRoundtrip :
        wordOfHash16
          (hash16OfWord
            (C13Concrete.forsPkWordC13 pk
              (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
              sigParsed.fors))
          =
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkByte :
      forsPk =
        hash16OfWord (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors = wordOfHash16 forsPk := by
    rw [hForsPkByte, hForsPkRoundtrip]
  exact accept_path_returns_verifyParsed_bool_from_named_fors_roots_and_layer_step_range
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hShape hZero hFors hFold hlen hg3 hgL hLeaf hmRlo hmRlast
    hForsPkWord hLayerStep hSpecFold hWordCmp

/-- Direct seed-cell plus named-root roundtrip form of the final accept adapter.
This is currently the narrowest named C13 FORS handoff: the caller supplies the
`afterFors` seed cell, named root cells, and the masked-word roundtrip fact. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_roundtrip_and_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkRoundtrip :
        wordOfHash16
          (hash16OfWord
            (C13Concrete.forsPkWordC13 pk
              (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
              sigParsed.fors))
          =
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkByte :
      forsPk =
        hash16OfWord (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors = wordOfHash16 forsPk := by
    rw [hForsPkByte, hForsPkRoundtrip]
  exact accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hShape hZero hFors hFold hlen hg3 hgL hmSeed hmRlo hmRlast
    hForsPkWord hLayerStep hSpecFold hWordCmp

/-! ## Named C13 accept-obligation bundle. -/

/-- Residual data/control obligations for the current narrow C13 accept handoff.

This packages the remaining post-parse model/spec correspondence surface after
`hFors`/`hFold` are known: the length and guard facts, the S4 seed/root frame,
the canonical FORS public-key roundtrip, the two-layer climb step/fold contract,
and the final word-comparison bridge.  It is intentionally only a bundle; every
field is still a real standalone obligation for later bridge work. -/
structure C13SeedNamedAcceptObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
            = wordNormalize 3688
  hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0
  hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      0 (wordNormalize 2)
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = (specRoot == pkRoot)

/-- Bundle-consuming form of the current narrow C13 accept adapter.  This is the
shape intended for final integration: parse/spec facts remain explicit, while
the still-open model/spec correspondence facts travel as one named contract. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  exact accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_roundtrip_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hShape hZero hFors hFold hObs.hlen hObs.hg3 hObs.hgL hObs.hmSeed
    hObs.hmRlo hObs.hmRlast hObs.hForsPkRoundtrip hObs.hLayerStep
    hObs.hSpecFold hObs.hWordCmp

/-- Successful concrete C13 parsing pins the ABI `sig_length` local to the C13
expected length.  This is the byte-spec length gate restated at the model-entry
state. -/
theorem c13_sig_length_of_parseSignatureC13
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
      = wordNormalize 3688 := by
  have hsz : sig.size = c13.sigBytes :=
    C13Concrete.parseSignatureC13_size hParse
  change sig.size = wordNormalize 3688
  rw [hsz]
  rfl

theorem c13_s3Guard_of_parse_forcedZero
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true) :
    SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0 := by
  let digestWord := keccakWords
    [ wordOfHash16 pkSeed
    , wordOfHash16 pkRoot
    , wordOfHash16 (read16 sig 0)
    , baToNatBE message % wordMod
    , hMsgPad ]
  have hR : sigParsed.R = read16 sig 0 :=
    C13Concrete.parseSignatureC13_R hParse
  have hIdxZero :
      (hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot } (read16 sig 0) message).forsIndex[6]?
        = some 0 := by
    have hz := C13Concrete.forcedZeroOk_c13_forsIndex_six
      (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) hZero
    rw [hPk, hR] at hz
    exact hz
  have hIdxFormula :
      (hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot } (read16 sig 0) message).forsIndex[6]?
        = some ((digestWord >>> 114) % 2 ^ 19) := by
    simpa [digestWord] using
      C13Concrete.hMsgC13_forsIndex_six
        { pkSeed := pkSeed, pkRoot := pkRoot } (read16 sig 0) message
  have hd0 : (digestWord >>> 114) % 2 ^ 19 = 0 := by
    rw [hIdxFormula] at hIdxZero
    injection hIdxZero
  have hdigest :
      lookupValue (afterS2 (mkC13State pkSeed pkRoot message sig)).bindings "digest"
        = digestWord := by
    unfold afterS2 digestWord
    exact SegmentS2R.s2_digest_mkC13State_final pkSeed pkRoot message sig
  have hbound : digestWord < 2 ^ 256 := by
    unfold digestWord
    have := SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
      [ wordOfHash16 pkSeed
      , wordOfHash16 pkRoot
      , wordOfHash16 (read16 sig 0)
      , baToNatBE message % wordMod
      , hMsgPad ]
    rwa [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl] at this
  rw [SegmentS3.s3Guard_eq_forsIndex6
    (afterS2 (mkC13State pkSeed pkRoot message sig)) digestWord hdigest hbound]
  exact hd0

/-- A one-layer C13 hypertree obligation that packages the control-flow guard
and the data relation together.  The genuine WOTS/XMSS correspondence should
prove this once per layer state: the model checksum guard passes, and the
post-layer `currentNode` tracks the spec step. -/
def LayerGuardedStep (specStep : Nat → ByteArray → ByteArray) : Prop :=
  ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
    CurrentNodeRel wordOfHash16 s node →
      SegmentLayer3.layerGuard
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true ∧
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node)

/-! ## Concrete C13 hypertree layer step

The accept-path bundles above intentionally quantify over an abstract
`specStep`.  The definitions and lemmas in this section instantiate that hook
with the concrete one-layer C13 WOTS/XMSS transition used by
`foldHypertree`.  They are still standalone: the actual model data-cell
correspondence is supplied by explicit hypotheses, and neither `execC13` nor the
byte-level bridge axiom is touched. -/

/-- The pre-shift hypertree index seen by layer `idx`, computed from the original
`H_msg` hypertree index. -/
def c13LayerTreeIdx (digest : HMsg) (idx : Nat) : Nat :=
  digest.hyperIndex / 2 ^ (c13.subtreeH * idx)

/-- The XMSS leaf index consumed by layer `idx`. -/
def c13LayerLeafIdx (digest : HMsg) (idx : Nat) : Nat :=
  c13LayerTreeIdx digest idx % 2 ^ c13.subtreeH

/-- The post-shift tree index used to address WOTS and XMSS at layer `idx`. -/
def c13LayerNextTree (digest : HMsg) (idx : Nat) : Nat :=
  c13LayerTreeIdx digest idx / 2 ^ c13.subtreeH

/-- Concrete byte-level C13 hypertree step for one layer.

On the accepting path this is the successful WOTS+C public-key reconstruction
followed by one XMSS root reconstruction.  The fallback branches make the
function total; accept-path lemmas use explicit hypotheses that rule them out. -/
def c13HypertreeSpecStep
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig) :
    Nat → ByteArray → ByteArray
  | idx, node =>
      match layers[idx]? with
      | none => node
      | some lsig =>
          let treeIdx := c13LayerNextTree digest idx
          let leafIdx := c13LayerLeafIdx digest idx
          if wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
              treeIdx leafIdx node lsig.wots then
            node
          else
            match C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
                treeIdx leafIdx node lsig.wots with
            | none => node
            | some wotsPk =>
                match C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
                    treeIdx leafIdx wotsPk lsig.authPath with
                | none => node
                | some root => root

/-- The concrete C13 step unfolds to the successful WOTS/XMSS root when the
corresponding layer, grinding check, WOTS reconstruction, and XMSS reconstruction
facts are supplied. -/
theorem c13HypertreeSpecStep_eq_root_of_success
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (idx : Nat) (node wotsPk root : ByteArray) (lsig : XmssLayerSig)
    (hLayer : layers[idx]? = some lsig)
    (hGrinding :
      wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots = false)
    (hWots :
      C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots
          = some wotsPk)
    (hXmss :
      C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) wotsPk lsig.authPath
          = some root) :
    c13HypertreeSpecStep pk digest layers idx node = root := by
  simp [c13HypertreeSpecStep, hLayer, hGrinding, hWots, hXmss]

/-- A reusable accept-path layer-step adapter: explicit guard and data-cell facts
for `SegmentLayer3.stepLayer` discharge `LayerGuardedStep` for the concrete C13
hypertree step.  The substantive WOTS/XMSS correspondence is isolated in
`hMerkleNode`, a direct post-step data-cell equality for `"merkleNode"`. -/
theorem layerGuardedStep_c13HypertreeSpecStep_of_merkleNode
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        SegmentLayer3.layerGuard
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true)
    (hMerkleNode : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        lookupValue
            (SegmentLayer3.stepLayer
              { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
            "merkleNode"
          = wordOfHash16 (c13HypertreeSpecStep pk digest layers idx node)) :
    LayerGuardedStep (c13HypertreeSpecStep pk digest layers) := by
  intro s node idx hRel
  refine ⟨hGuard s node idx hRel, ?_⟩
  exact CurrentNodeFrame.stepLayer_currentNodeRel_of_merkleNode
    s (c13HypertreeSpecStep pk digest layers) node idx
    (hMerkleNode s node idx hRel)

/-- A single successful concrete layer fact is enough to rewrite the
post-`stepLayer` `"currentNode"` relation to the successful XMSS root. -/
theorem stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (s : RuntimeState) (idx : Nat) (node wotsPk root : ByteArray) (lsig : XmssLayerSig)
    (hLayer : layers[idx]? = some lsig)
    (hGrinding :
      wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots = false)
    (hWots :
      C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots
          = some wotsPk)
    (hXmss :
      C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) wotsPk lsig.authPath
          = some root)
    (hMerkleNode :
      lookupValue
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
          "merkleNode"
        = wordOfHash16 root) :
    CurrentNodeRel wordOfHash16
      (SegmentLayer3.stepLayer
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
      (c13HypertreeSpecStep pk digest layers idx node) := by
  rw [c13HypertreeSpecStep_eq_root_of_success
    pk digest layers idx node wotsPk root lsig hLayer hGrinding hWots hXmss]
  exact CurrentNodeFrame.stepLayer_currentNodeRel_of_merkleNode
    s (fun _ _ => root) node idx hMerkleNode

theorem layerGuardsPass_of_guarded_step
    (pkSeed pkRoot message sig : ByteArray)
    (forsPk : ByteArray) (specStep : Nat → ByteArray → ByteArray)
    (hStart : CurrentNodeRel wordOfHash16
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      forsPk)
    (hLayerGuardStep : LayerGuardedStep specStep) :
    ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      0 (wordNormalize 2) :=
  ClimbLoopGuarded.allGuardsPass_of_rel "layer" SegmentLayer3.stepLayer
    SegmentLayer3.layerGuard specStep (CurrentNodeRel wordOfHash16)
    hLayerGuardStep _ forsPk 0 (wordNormalize 2) hStart

theorem layerStep_of_guarded_step
    (specStep : Nat → ByteArray → ByteArray)
    (hLayerGuardStep : LayerGuardedStep specStep) :
    ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node) := by
  intro s node idx h
  exact (hLayerGuardStep s node idx h).2

/-- The initial C13 layer-loop relation follows from the named S4/FORS frame.

This packages the S4 compression adapters with the seed assignment: once the
`afterFors` seed cell, the six normal root cells, the forced-root cell, and the
canonical named-FORS roundtrip are known, `afterSeed`'s `"currentNode"` binding
already tracks the spec-side `forsPk`.  The following guarded-layer handoff can
therefore start from S4/FORS facts directly instead of carrying a separate
`hLayerStart` premise. -/
theorem layerStart_of_seed_named_fors_roots_roundtrip
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk : ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkRoundtrip :
        wordOfHash16
          (hash16OfWord
            (C13Concrete.forsPkWordC13 pk
              (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
              sigParsed.fors))
          =
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors) :
    CurrentNodeRel wordOfHash16
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      forsPk := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkByte :
      forsPk =
        hash16OfWord (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors = wordOfHash16 forsPk := by
    rw [hForsPkByte, hForsPkRoundtrip]
  have hForsPkCompress :
      C13Concrete.maskN
        (C13Concrete.keccakWords
          (C13Concrete.wordOfHash16 pkSeed :: C13Concrete.adrsForsRoots ::
            C13Concrete.forsAllRootsC13 pk digest sigParsed.fors))
        = C13Concrete.wordOfHash16 forsPk := by
    subst hPk
    simpa [digest, C13Concrete.forsPkWordC13] using hForsPkWord
  have hForsCompress :
      CurrentNodeFrame.forsPkCompressWord
        (afterFors (mkC13State pkSeed pkRoot message sig)) = wordOfHash16 forsPk := by
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_seed_mkC13State_six_plus_last
      pkSeed pkRoot message sig (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
      (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors) hmSeed]
    · exact hForsPkCompress
    · intro j hj
      simpa [digest] using hmRlo j hj
    · simpa [digest] using hmRlast
  have hForsPkFinal :
      lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings "forsPk"
        = wordOfHash16 forsPk :=
    CurrentNodeFrame.afterFinalize_forsPk_of_compress
      (mkC13State pkSeed pkRoot message sig) forsPk hForsCompress
  unfold CurrentNodeRel
  rw [MemoryKit.lookupValue_bindValue_ne
    (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
    "layer" "currentNode" (wordNormalize 0) (by decide)]
  rw [CurrentNodeFrame.afterSeed_currentNode]
  exact hForsPkFinal

/-- The same residual C13 accept-obligation bundle as
`C13SeedNamedAcceptObligations`, but with the length guard omitted.  Use this
when a successful concrete C13 parse is already available; the corresponding
`sig_length = 3688` model fact is supplied by
`c13_sig_length_of_parseSignatureC13`. -/
structure C13SeedNamedAcceptDataObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0
  hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      0 (wordNormalize 2)
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = (specRoot == pkRoot)

/-- The current parse-and-forced-zero based C13 accept-obligation bundle.  Both
the length guard and the S3 forced-zero guard are omitted: successful concrete
C13 parsing supplies the length fact, and
`c13_s3Guard_of_parse_forcedZero` supplies the S3 guard from the same parse fact
plus the spec-side `forcedZeroOk` hypothesis. -/
structure C13SeedNamedAcceptParsedObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      0 (wordNormalize 2)
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = (specRoot == pkRoot)

/-- A tighter parsed handoff that replaces the separate layer-loop guard trace
and layer-step relation with one guarded per-layer correspondence plus the
already-derived start relation. -/
structure C13SeedNamedAcceptGuardedLayerObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerStart : CurrentNodeRel wordOfHash16
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      forsPk
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = (specRoot == pkRoot)

/-- Parsed guarded-layer C13 obligations with the layer start relation derived
from the S4/FORS frame instead of supplied separately. -/
structure C13SeedNamedAcceptGuardedObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = (specRoot == pkRoot)

/-- Byte-shaped guarded C13 obligations with the final word comparison reduced
to canonical root roundtrips.  This is the same residual surface as
`C13SeedNamedAcceptGuardedObligations`, except callers no longer supply
`hWordCmp` directly. -/
structure C13SeedNamedAcceptGuardedRoundtripObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hSpecRootRoundtrip : hash16OfWord (wordOfHash16 specRoot) = specRoot
  hPkRootRoundtrip : hash16OfWord (wordOfHash16 pkRoot) = pkRoot

/-- Byte-shaped guarded C13 obligations after deriving the C13-produced
spec-root roundtrip from successful FORS reconstruction and hypertree folding.
The public key root remains a boundary premise because C13 imposes no byte-level
canonicality check on `pkRoot`. -/
structure C13SeedNamedAcceptGuardedPkRoundtripObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootRoundtrip : hash16OfWord (wordOfHash16 pkRoot) = pkRoot

/-- Byte-shaped guarded C13 obligations after deriving both C13-produced
roundtrips internally: the FORS public-key compression word is a masked Keccak
word, and the spec-root byte roundtrip follows from successful reconstruction.
The public key root remains a boundary premise because C13 imposes no byte-level
canonicality check on `pkRoot`. -/
structure C13SeedNamedAcceptGuardedPkRootObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootRoundtrip : hash16OfWord (wordOfHash16 pkRoot) = pkRoot

/-- Byte-shaped guarded C13 obligations with the public-key root boundary stated
as the SPHINCS+ byte width rather than the derived C13 byte-roundtrip equation. -/
structure C13SeedNamedAcceptGuardedPkRootSizeObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootSize : pkRoot.size = 16

/-- Byte-shaped guarded C13 obligations where the seed cell needed by FORS
public-key compression is derived from a range-gated one-step FORS leaf frame.
The remaining FORS root cells are still the substantive S4 correspondence
obligations. -/
structure C13SeedNamedAcceptGuardedPkRootSizeLeafObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootSize : pkRoot.size = 16

/-- Parse-based bundle-consuming form of the current narrow C13 accept adapter.
Successful `parseSignatureC13` supplies the length guard; all remaining data
correspondence obligations stay explicit in
`C13SeedNamedAcceptDataObligations`. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_data_obligations_of_parse
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptDataObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  refine accept_path_returns_verifyParsed_bool_from_seed_named_obligations
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hShape hZero hFors hFold ?_
  exact
    { hlen := c13_sig_length_of_parseSignatureC13 pkSeed pkRoot message sig sigParsed hParse
      hg3 := hObs.hg3
      hgL := hObs.hgL
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hLayerStep := hObs.hLayerStep
      hSpecFold := hObs.hSpecFold
      hWordCmp := hObs.hWordCmp }

theorem accept_path_returns_verifyParsed_bool_from_seed_named_parsed_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptParsedObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  refine accept_path_returns_verifyParsed_bool_from_seed_named_data_obligations_of_parse
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hParse hShape hZero hFors hFold ?_
  exact
    { hg3 := c13_s3Guard_of_parse_forcedZero
        pkSeed pkRoot message sig pk sigParsed hPk hParse hZero
      hgL := hObs.hgL
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hLayerStep := hObs.hLayerStep
      hSpecFold := hObs.hSpecFold
      hWordCmp := hObs.hWordCmp }

theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_layer_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedLayerObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  refine accept_path_returns_verifyParsed_bool_from_seed_named_parsed_obligations
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hParse hShape hZero hFors hFold ?_
  exact
    { hgL := layerGuardsPass_of_guarded_step
        pkSeed pkRoot message sig forsPk specStep hObs.hLayerStart hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hLayerStep := layerStep_of_guarded_step specStep hObs.hLayerGuardStep
      hSpecFold := hObs.hSpecFold
      hWordCmp := hObs.hWordCmp }

theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  refine accept_path_returns_verifyParsed_bool_from_seed_named_guarded_layer_obligations
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hParse hShape hZero hFors hFold ?_
  exact
    { hLayerStart := layerStart_of_seed_named_fors_roots_roundtrip
        pkSeed pkRoot message sig pk sigParsed forsPk hPk hFors hObs.hmSeed
        hObs.hmRlo hObs.hmRlast hObs.hForsPkRoundtrip
      hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hSpecFold := hObs.hSpecFold
      hWordCmp := hObs.hWordCmp }

/-- Same as `accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations`,
but derives the C13 `signatureShapeOk` guard from successful concrete parsing.
This is the current narrowest parse-based accept handoff: the caller supplies
parse, forced-zero, FORS, fold, and the remaining model/spec correspondence
bundle, but no separate signature-shape fact. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_parse
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState :=
  accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hParse (C13Concrete.parseSignatureC13_shape hParse) hZero hFors hFold hObs

/-- Byte-shaped form of the current C13 accept handoff.  The public key is the
one obtained from the two byte-level public-key arguments, so callers no longer
need to pass the record-equality side condition separately. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedObligations
        pkSeed pkRoot message sig
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (specRoot == pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pkRoot))) finalState := by
  simpa using
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_parse
      pkSeed pkRoot message sig
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed forsPk specRoot specStep
      rfl hParse hZero hFors hFold hObs

/-- Byte-shaped guarded handoff with the final comparison discharged from
canonical root roundtrips. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_roundtrip_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedRoundtripObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (specRoot == pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hSpecFold := hObs.hSpecFold
      hWordCmp :=
        wordCmp_of_wordOfHash16_roundtrip specRoot pkRoot
          hObs.hSpecRootRoundtrip hObs.hPkRootRoundtrip }

/-- Byte-shaped guarded handoff with the C13-produced spec-root roundtrip
derived internally from `hFors` and `hFold`.  The only final comparison
roundtrip premise left in the bundle is the public-key root roundtrip. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_roundtrip_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRoundtripObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (specRoot == pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_roundtrip_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hSpecFold := hObs.hSpecFold
      hSpecRootRoundtrip :=
        specRoot_roundtrip_of_c13_fors_fold hFors hFold
      hPkRootRoundtrip := hObs.hPkRootRoundtrip }

/-- Byte-shaped guarded handoff after deriving the FORS public-key masked-word
roundtrip and the C13-produced spec-root byte roundtrip internally.  The only
roundtrip premise left in the bundle is for the public-key root. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRootObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (specRoot == pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_roundtrip_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := forsPkWordC13_roundtrip
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors
      hSpecFold := hObs.hSpecFold
      hPkRootRoundtrip := hObs.hPkRootRoundtrip }

/-- Byte-shaped guarded handoff with the public-key-root byte roundtrip derived
from the ordinary 16-byte SPHINCS+ root width. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRootSizeObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (specRoot == pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hSpecFold := hObs.hSpecFold
      hPkRootRoundtrip := hash16OfWord_wordOfHash16_of_size pkRoot hObs.hPkRootSize }

/-- Byte-shaped guarded handoff with the seed-cell premise derived from a
range-gated FORS leaf-step preservation fact. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRootSizeLeafObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (specRoot == pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed :=
        CurrentNodeFrame.afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves
          pkSeed pkRoot message sig hObs.hLeaf
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hSpecFold := hObs.hSpecFold
      hPkRootSize := hObs.hPkRootSize }

/-! ## Axiom audit. -/

#print axioms accept_path_returns_verifyParsed_bool
#print axioms accept_path_returns_verifyParsed_bool_linked
#print axioms verifyParsed_ok_branch
#print axioms accept_path_returns_verifyParsed_bool_from_root
#print axioms wordCmp_of_wordOfHash16_iff
#print axioms hash16OfWord_beq_eq_decide
#print axioms byteRoot_beq_eq_decide_of_wordOfHash16_roundtrip
#print axioms wordCmp_of_wordOfHash16_roundtrip
#print axioms uint8_toNat_ofNat
#print axioms base256_digit_append
#print axioms base256_digit_decomp
#print axioms base256_uint8_fold_init
#print axioms base256_uint8_fold_lt
#print axioms base256_fold_digit_of_list
#print axioms baToNatBE_eq_data_toList
#print axioms baToNatBE_lt_of_size
#print axioms hash16OfWord_wordOfHash16_of_size
#print axioms highDigitsFold_eq_mod
#print axioms highHalf_mod_digit
#print axioms hash16OfWord_wordOfHash16_hash16OfWord
#print axioms baToNatBE_hash16OfWord
#print axioms wordOfHash16_hash16OfWord_highHalf
#print axioms wordOfHash16_hash16OfWord_maskN_of_lt
#print axioms forsPkWordC13_roundtrip
#print axioms hash16OfWord_wordOfHash16_of_canonical
#print axioms specRoot_roundtrip_of_c13_fors_fold
#print axioms accept_path_returns_verifyParsed_bool_from_layer_step
#print axioms accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step
#print axioms accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range
#print axioms accept_path_returns_verifyParsed_bool_from_seed_and_fors_roots_and_layer_step
#print axioms accept_path_returns_verifyParsed_bool_from_named_fors_roots_and_layer_step_range
#print axioms accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_and_layer_step
#print axioms accept_path_returns_verifyParsed_bool_from_named_fors_roots_roundtrip_and_layer_step_range
#print axioms accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_roundtrip_and_layer_step
#print axioms C13SeedNamedAcceptObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_obligations
#print axioms c13_sig_length_of_parseSignatureC13
#print axioms c13_s3Guard_of_parse_forcedZero
#print axioms LayerGuardedStep
#print axioms c13HypertreeSpecStep_eq_root_of_success
#print axioms layerGuardedStep_c13HypertreeSpecStep_of_merkleNode
#print axioms stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success
#print axioms layerGuardsPass_of_guarded_step
#print axioms layerStep_of_guarded_step
#print axioms layerStart_of_seed_named_fors_roots_roundtrip
#print axioms C13SeedNamedAcceptDataObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_data_obligations_of_parse
#print axioms C13SeedNamedAcceptParsedObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_parsed_obligations
#print axioms C13SeedNamedAcceptGuardedLayerObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_layer_obligations
#print axioms C13SeedNamedAcceptGuardedObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_parse
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedRoundtripObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_roundtrip_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedPkRoundtripObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_roundtrip_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedPkRootObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedPkRootSizeObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedPkRootSizeLeafObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_obligations_of_bytes

end SphincsMinusVerifiers.SegmentAcceptSpec
