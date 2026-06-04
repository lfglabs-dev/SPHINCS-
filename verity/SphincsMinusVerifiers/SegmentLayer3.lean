/-
  SegmentLayer3 — the Layer-3 hypertree-climb loop body (statement 25 of
  `c13VerifyBody`, the `forEach "layer" (u 2)` outer climb).

  The layer body is *guarded*: after accumulating the WOTS checksum `digitSum`
  it reverts unless `digitSum = 208` (Model.lean:167).  So unlike the totally
  continuing FORS/Merkle loops, this body has the shape

  ```
  execStmtList [] ls layerBody = if layerGuard ls then .continue (stepLayer ls) else .revert
  ```

  proved here as `execLayerBody`.  This is exactly the `hstep` hypothesis of the
  guarded loop-threading engine `ClimbLoopGuarded.execForEachLoop_of_guarded_step`,
  so once the per-iteration guards are discharged the whole `forEach "layer"`
  folds to a pure `foldLoop` over `stepLayer` (`execLayerLoop`).

  Faithfulness is machine-checked: `layerStmt_eq_slice` (`rfl`) shows the
  reconstructed statement — loop header and full body, every inner `forEach` and
  the checksum-guard `ite` included — is exactly statement 25 of `c13VerifyBody`.
  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ClimbLoopGuarded
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.Model
import SphincsMinusVerifiers.SegmentS2
import SphincsMinusVerifiers.StateFrame
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentLayer3

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (N_MASK merkleClimbBody wotsChainBody stepMerkle stepWots
  wotsChainStep execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue execStmt_letVar_continue)
open SphincsMinusVerifiers.ClimbLoop (foldLoop execStmt_forEach_of_step execStmt_forEach_merkleClimb)
open SphincsMinusVerifierSpec.C13Concrete (wotsDigitSum)
open SphincsMinusVerifiers.BindingFrame

/-! ## 0. EDSL constructors (matching `Model.lean`'s private helpers). -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def notE (x : Expr) : Expr := .logicalNot x
private def eqE (a b : Expr) : Expr := .eq a b
private def addE (a b : Expr) : Expr := .add a b
private def subE (a b : Expr) : Expr := .sub a b
private def mulE (a b : Expr) : Expr := .mul a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def xorE (a b : Expr) : Expr := .bitXor a b
private def shlE (a b : Expr) : Expr := .shl a b
private def shrE (a b : Expr) : Expr := .shr a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def cdload (off : Expr) : Expr := .calldataload off
private def mloadE (off : Expr) : Expr := .mload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val

private def revert0 : List Stmt :=
  [ .unsafeYul <|
      UnsafeYulFragment.rawRevert (.lit 0) (.lit 0)
        { name := "raw_yul_revert_0_0_refines_solidity_assembly"
          obligation := "The handwritten Yul revert(0, 0) must match the Solidity assembly observable revert behavior."
          proofStatus := .assumed }
        "raw_yul_revert_0_0" ]

/-- The checksum-guard condition: `digitSum ≠ 208`. -/
private def condE : Expr := notE (eqE (v "digitSum") (u 208))

/-! ## 1. Per-statement `.continue` combinator for `assignVar`. -/

/-- `assignVar` shares the interpreter's `letVar` step semantics. -/
private theorem assignVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.assignVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

/-! ## 2. Inner-loop body step lemmas. -/

/-- The digit-sum accumulation loop body (`forEach "ii" (u 43)`). -/
def digitSumBody : List Stmt :=
  [ .assignVar "digitSum" (addE (v "digitSum") (andE (shrE (mulE (v "ii") (u 3)) (v "d")) (u 0x7))) ]

def digitSumStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st digitSumBody with | .continue s' => s' | _ => st

theorem digitSumStepLemma (st : RuntimeState) :
    execStmtList [] st digitSumBody = .continue (digitSumStep st) := by
  unfold digitSumStep digitSumBody
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue st "digitSum" _ _ rfl)]
  rfl

/-- One executable digit-sum iteration stores the value of the checksum update
expression.  This is the per-step data fact needed before reducing the
`forEach "ii" 43` checksum loop to `C13Concrete.wotsDigitSum`. -/
theorem digitSumStep_digitSum_expr (st : RuntimeState) :
    lookupValue (digitSumStep st).bindings "digitSum" =
      (evalExpr [] st
        (addE (v "digitSum") (andE (shrE (mulE (v "ii") (u 3)) (v "d")) (u 0x7)))).getD 0 := by
  unfold digitSumStep digitSumBody addE andE shrE mulE v u
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue st "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_self]
  rfl

/-- One checksum-loop step only writes `"digitSum"`. -/
theorem digitSumStep_preserves_lookup_of_ne
    (st : RuntimeState) (key : String) (hne : key ≠ "digitSum") :
    lookupValue (digitSumStep st).bindings key = lookupValue st.bindings key := by
  unfold digitSumStep digitSumBody addE andE shrE mulE v u
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue st "digitSum" _ _ rfl)]
  simp only [execStmtList]
  exact MemoryKit.lookupValue_bindValue_ne _ "digitSum" key _
    (fun h => hne h.symm)

/-- Low-three-bit mask used by the WOTS+C checksum loop. -/
theorem nat_land_low3 (x : Nat) : Nat.land x 0x7 = x % 8 := by
  change (x &&& (2 ^ 3 - 1)) = x % 2 ^ 3
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 3
  · have hmask : (2 ^ 3 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 3 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

/-- Low-eleven-bit mask used by the C13 hypertree layer split. -/
theorem nat_land_low11 (x : Nat) : Nat.land x 0x7FF = x % 2 ^ 11 := by
  change (x &&& (2 ^ 11 - 1)) = x % 2 ^ 11
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 11
  · have hmask : (2 ^ 11 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 11 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

/-- One checksum-loop iteration adds the low 3-bit digit selected by `"ii"`.
The bound hypotheses are exactly the C13 checksum range (`43 * 7 < 2^256`) and
the EVM word bound for `"d"`. -/
theorem digitSumStep_digitSum_eq_add_digit
    (st : RuntimeState) (i acc d : Nat)
    (hii : lookupValue st.bindings "ii" = i)
    (hacc : lookupValue st.bindings "digitSum" = acc)
    (hd : lookupValue st.bindings "d" = d)
    (hi : i < 43)
    (haccBound : acc ≤ 7 * i)
    (hdBound : d < 2 ^ 256) :
    lookupValue (digitSumStep st).bindings "digitSum" =
      acc + ((d >>> (3 * i)) % 8) := by
  rw [digitSumStep_digitSum_expr]
  unfold addE andE shrE mulE v u
  have hmul : evalExpr [] st (.mul (.localVar "ii") (.literal 3)) = some (i * 3) := by
    have hiWord : i < 2 ^ 256 := lt_trans hi (by decide : 43 < 2 ^ 256)
    have h3 : wordNormalize 3 = 3 := by
      rw [wordNormalize_eq_mod]
      exact Nat.mod_eq_of_lt (by decide : 3 < 2 ^ 256)
    change (do
      let lhs : Verity.Core.Uint256 := ← some (lookupValue st.bindings "ii")
      let rhs : Verity.Core.Uint256 := ← some (wordNormalize 3)
      pure (lhs * rhs).val) = some (i * 3)
    rw [hii, h3]
    show some ((Verity.Core.Uint256.ofNat i * Verity.Core.Uint256.ofNat 3).val)
      = some (i * 3)
    show some (((Verity.Core.Uint256.ofNat i).val * (Verity.Core.Uint256.ofNat 3).val)
        % Verity.Core.Uint256.modulus) = some (i * 3)
    have hiv : (Verity.Core.Uint256.ofNat i).val = i := Nat.mod_eq_of_lt hiWord
    have h3v : (Verity.Core.Uint256.ofNat 3).val = 3 := Nat.mod_eq_of_lt (by decide : 3 < 2 ^ 256)
    have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
    rw [hiv, h3v, hmod, Nat.mod_eq_of_lt]
    exact lt_trans (Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 3))
      (by decide : 43 * 3 < 2 ^ 256)
  have hshr : evalExpr [] st (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d"))
      = some (d >>> (i * 3)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      st (.mul (.localVar "ii") (.literal 3)) (.localVar "d")
      (i * 3) d hmul (by
        change some (lookupValue st.bindings "d") = some d
        rw [hd])
      (lt_trans (Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 3))
        (by decide : 43 * 3 < 2 ^ 256))
      hdBound
  have hland : evalExpr [] st
      (.bitAnd (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d")) (.literal 7))
        = some ((d >>> (i * 3)) % 8) := by
    have hraw :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
        st (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d"))
        (d >>> (i * 3)) 7 hshr
        (by
          rw [Nat.shiftRight_eq_div_pow]
          exact Nat.lt_of_le_of_lt (Nat.div_le_self d (2 ^ (i * 3))) hdBound)
        (by decide : 7 < 2 ^ 256)
    rw [hraw, nat_land_low3]
  have hadd : evalExpr [] st
      (.add (.localVar "digitSum")
        (.bitAnd (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d")) (.literal 7)))
      = some (acc + ((d >>> (i * 3)) % 8) ) := by
    refine SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st (.localVar "digitSum")
      (.bitAnd (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d")) (.literal 7))
      acc ((d >>> (i * 3)) % 8) (by
        change some (lookupValue st.bindings "digitSum") = some acc
        rw [hacc]) hland ?_ ?_ ?_
    · exact lt_of_le_of_lt haccBound
        (by
          have : 7 * i < 7 * 43 := by omega
          exact lt_trans this (by decide : 7 * 43 < 2 ^ 256))
    · exact lt_trans (Nat.mod_lt _ (by decide : 0 < 8)) (by decide : 8 < 2 ^ 256)
    · have hdigit : (d >>> (i * 3)) % 8 < 8 := Nat.mod_lt _ (by decide : 0 < 8)
      exact lt_of_le_of_lt (Nat.add_le_add haccBound (Nat.le_of_lt_succ hdigit))
        (by
          have : 7 * i + 7 ≤ 7 * 43 := by omega
          exact lt_of_le_of_lt this (by decide : 7 * 43 < 2 ^ 256))
  rw [hadd]
  simp only [Option.getD_some]
  rw [Nat.mul_comm i 3]

/-- The WOTS-chain outer-loop body (`forEach "i" (u 43)`), with its inner
variable-bound chain `forEach "step" (v "steps")` written as `wotsChainBody`. -/
def wotsOuterBody : List Stmt :=
  [ .letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 0x7))
  , .letVar "steps" (subE (u 7) (v "digit"))
  , .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
  , .letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i")))
  , .forEach "step" (v "steps") wotsChainBody
  , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ]

/-- The WOTS outer-loop body before the final public-key scratch store. -/
def wotsOuterPrefix : List Stmt :=
  [ .letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 0x7))
  , .letVar "steps" (subE (u 7) (v "digit"))
  , .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
  , .letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i")))
  , .forEach "step" (v "steps") wotsChainBody ]

def wotsOuterStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st wotsOuterBody with | .continue s' => s' | _ => st

theorem wotsOuterStepLemma (st : RuntimeState) :
    execStmtList [] st wotsOuterBody = .continue (wotsOuterStep st) := by
  unfold wotsOuterStep wotsOuterBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "digit" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "steps" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "val" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "chainBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "step" (v "steps") wotsChainBody _ _ stepWots rfl wotsChainStep)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- One WOTS chain step preserves lookups other than its `"val"` assignment. -/
theorem stepWots_preserves_lookup_of_ne
    (st : RuntimeState) (key : String) (hne : "val" ≠ key) :
    lookupValue (stepWots st).bindings key =
      lookupValue st.bindings key := by
  refine execStmtList_preserves_lookup key wotsChainBody st (stepWots st) ?_
    (wotsChainStep st)
  intro s s'' stmt hmem hexec
  simp [wotsChainBody] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact execStmt_mstore_preserves_lookup s s'' key _ _ hexec
  · exact execStmt_mstore_preserves_lookup s s'' key _ _ hexec
  · exact execStmt_assignVar_preserves_lookup s s'' "val" key _ hne hexec

/-- The WOTS-pk copy loop body (`forEach "i" (u 43)`). -/
def copyBody : List Stmt :=
  [ mstoreE (addE (u 0x40) (shlE (u 5) (v "i"))) (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) ]

def copyStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st copyBody with | .continue s' => s' | _ => st

theorem copyStepLemma (st : RuntimeState) :
    execStmtList [] st copyBody = .continue (copyStep st) := by
  unfold copyStep copyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- One WOTS chain step only writes scratch cells `0x20` and `0x40`, so it
preserves seed cell `0x00`. -/
theorem stepWots_preserves_memory_zero (st : RuntimeState) :
    ((stepWots st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 wotsChainBody st (stepWots st) ?_ (wotsChainStep st)
  intro s s'' stmt hmem hexec
  simp [wotsChainBody] at hmem
  rcases hmem with rfl | rfl | rfl
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 _ _ ?_ hexec
    intro ro rv hoff hval
    cases hoff
    decide
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 _ _ ?_ hexec
    intro ro rv hoff hval
    cases hoff
    decide
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
      s s'' 0x00 "val" _ hexec

/-- A folded WOTS chain preserves seed cell `0x00`. -/
theorem wotsChainFold_preserves_memory_zero (st : RuntimeState) (n : Nat) :
    ((foldLoop "step" stepWots
        { st with bindings := bindValue st.bindings "step" (wordNormalize 0) }
        0 (wordNormalize n)).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val
    "step" stepWots 0x00 stepWots_preserves_memory_zero
    { st with bindings := bindValue st.bindings "step" (wordNormalize 0) }
    0 (wordNormalize n)]

/-- A folded WOTS chain preserves outer-loop index `"i"`. -/
theorem wotsChainFold_preserves_i_lookup (st : RuntimeState) (n : Nat) :
    lookupValue
        (foldLoop "step" stepWots
          { st with bindings := bindValue st.bindings "step" (wordNormalize 0) }
          0 n).bindings "i" =
      lookupValue st.bindings "i" := by
  rw [ClimbLoop.foldLoop_preserves_lookup "step" "i" stepWots (by decide)
    (fun s => stepWots_preserves_lookup_of_ne s "i" (by decide))
    { st with bindings := bindValue st.bindings "step" (wordNormalize 0) }
    0 n]
  exact MemoryKit.lookupValue_bindValue_ne st.bindings "step" "i" (wordNormalize 0) (by decide)

/-- The WOTS outer prefix preserves seed cell `0x00`. -/
theorem wotsOuterPrefix_preserves_memory_zero
    (st s' : RuntimeState)
    (hExec : execStmtList [] st wotsOuterPrefix = .continue s') :
    (s'.world.memory 0x00).val = (st.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 wotsOuterPrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp [wotsOuterPrefix] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "digit" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "steps" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "val" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "chainBase" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val
      "step" 0x00 (v "steps") wotsChainBody s s'' ?_ hexec
    intro t t'' stmt hmem' hexec'
    simp [wotsChainBody] at hmem'
    rcases hmem' with rfl | rfl | rfl
    · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
        t t'' 0x00 _ _ ?_ hexec'
      intro ro rv hoff hval
      cases hoff
      decide
    · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
        t t'' 0x00 _ _ ?_ hexec'
      intro ro rv hoff hval
      cases hoff
      decide
    · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
        t t'' 0x00 "val" _ hexec'

/-- The WOTS outer prefix preserves the outer-loop index binding `"i"`. -/
theorem wotsOuterPrefix_preserves_i_lookup
    (st s' : RuntimeState)
    (hExec : execStmtList [] st wotsOuterPrefix = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i" wotsOuterPrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp [wotsOuterPrefix] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup s s'' "digit" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "steps" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "val" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "chainBase" "i" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "step" "i" _ _ s s'' (by decide)
      (by
        intro t t'' stmt hmem' hexec'
        simp [wotsChainBody] at hmem'
        rcases hmem' with rfl | rfl | rfl
        · exact execStmt_mstore_preserves_lookup t t'' "i" _ _ hexec'
        · exact execStmt_mstore_preserves_lookup t t'' "i" _ _ hexec'
        · exact execStmt_assignVar_preserves_lookup t t'' "val" "i" _ (by decide) hexec')
      hexec

/-- Executing one WOTS outer-loop body preserves seed cell `0x00` for the actual
C13 outer-loop index range. -/
theorem wotsOuterBody_preserves_memory_zero_of_i
    (st s' : RuntimeState) (i : Nat)
    (hi : i < 43)
    (hI : lookupValue st.bindings "i" = wordNormalize i)
    (hExec : execStmtList [] st wotsOuterBody = .continue s') :
    (s'.world.memory 0x00).val = (st.world.memory 0x00).val := by
  have hSplit :
      wotsOuterBody =
        wotsOuterPrefix ++
          [mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")] := rfl
  rw [hSplit, MemoryKit.execStmtList_append] at hExec
  cases hPrefix : execStmtList [] st wotsOuterPrefix with
  | «continue» mid =>
      rw [hPrefix] at hExec
      have hPrefixMem := wotsOuterPrefix_preserves_memory_zero st mid hPrefix
      have hPrefixI := wotsOuterPrefix_preserves_i_lookup st mid hPrefix
      have hINorm : wordNormalize i = i :=
        SegmentS2.wordNormalize_of_lt (lt_trans hi (by decide : 43 < 2 ^ 256))
      have hIeval : evalExpr [] mid (v "i") = some i := by
        change some (lookupValue mid.bindings "i") = some i
        rw [hPrefixI, hI, hINorm]
      have hShiftBound : i <<< 5 < 2 ^ 256 := by
        rw [Nat.shiftLeft_eq]
        have : i * 2 ^ 5 < 43 * 2 ^ 5 := by
          exact Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 2 ^ 5)
        exact lt_trans this (by decide : 43 * 2 ^ 5 < 2 ^ 256)
      have hShift :
          evalExpr [] mid (shlE (u 5) (v "i")) = some (i <<< 5) := by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
          mid (u 5) (v "i") 5 i rfl hIeval
          (by decide : 5 < 2 ^ 256)
          (lt_trans hi (by decide : 43 < 2 ^ 256))
          hShiftBound
      have hOff :
          evalExpr [] mid (addE (u 0x80) (shlE (u 5) (v "i"))) =
            some (0x80 + (i <<< 5)) := by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
          mid (u 0x80) (shlE (u 5) (v "i")) 0x80 (i <<< 5)
          rfl hShift (by decide : 0x80 < 2 ^ 256) hShiftBound
          (by
            rw [Nat.shiftLeft_eq]
            have : 0x80 + i * 2 ^ 5 < 0x80 + 43 * 2 ^ 5 := by omega
            exact lt_trans this (by decide : 0x80 + 43 * 2 ^ 5 < 2 ^ 256))
      have hVal : evalExpr [] mid (v "val") = some (lookupValue mid.bindings "val") := rfl
      let mid' : RuntimeState :=
        { mid with world := { mid.world with
          memory := MemoryKit.memUpdate mid.world.memory (0x80 + (i <<< 5))
            (lookupValue mid.bindings "val") } }
      have hStore :
          execStmt [] mid
              (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) =
            .continue mid' := by
        unfold mid' mstoreE
        exact execStmt_mstore_continue mid
          (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
          (0x80 + (i <<< 5)) (lookupValue mid.bindings "val") hOff hVal
      change
        (match execStmt [] mid
            (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) with
          | .continue n => execStmtList [] n []
          | .stop n => .stop n
          | .return rv rs => .return rv rs
          | .revert => .revert) = .continue s' at hExec
      rw [hStore] at hExec
      simp only [execStmtList] at hExec
      injection hExec with hs'
      subst s'
      unfold mid'
      change
        (MemoryKit.memUpdate mid.world.memory (0x80 + (i <<< 5))
            (lookupValue mid.bindings "val") 0x00).val =
          (st.world.memory 0x00).val
      rw [MemoryKit.memUpdate_diff _ (0x80 + (i <<< 5)) 0x00 _ (by omega)]
      exact hPrefixMem
  | stop stopped =>
      rw [hPrefix] at hExec
      simp at hExec
  | «return» rv rst =>
      rw [hPrefix] at hExec
      simp at hExec
  | revert =>
      rw [hPrefix] at hExec
      simp at hExec

/-- One WOTS outer-loop step preserves seed cell `0x00` for the actual C13
outer-loop index range. -/
theorem wotsOuterStep_preserves_memory_zero_of_i
    (st : RuntimeState) (i : Nat)
    (hi : i < 43)
    (hI : lookupValue st.bindings "i" = wordNormalize i) :
    ((wotsOuterStep st).world.memory 0x00).val =
      (st.world.memory 0x00).val :=
  wotsOuterBody_preserves_memory_zero_of_i st (wotsOuterStep st) i hi hI
    (wotsOuterStepLemma st)

/-- Executing one WOTS outer-loop body preserves the outer-loop index binding
`"i"`. -/
theorem wotsOuterBody_preserves_i_lookup (st s' : RuntimeState)
    (hExec : execStmtList [] st wotsOuterBody = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i" wotsOuterBody st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp [wotsOuterBody] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup s s'' "digit" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "steps" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "val" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "chainBase" "i" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "step" "i" _ _ s s'' (by decide)
      (by
        intro s' s''' stmt hmem' hexec'
        simp [wotsChainBody] at hmem'
        rcases hmem' with rfl | rfl | rfl
        · exact execStmt_mstore_preserves_lookup s' s''' "i" _ _ hexec'
        · exact execStmt_mstore_preserves_lookup s' s''' "i" _ _ hexec'
        · exact execStmt_assignVar_preserves_lookup s' s''' "val" "i" _ (by decide) hexec')
      hexec
  · exact execStmt_mstore_preserves_lookup s s'' "i" _ _ hexec

/-- One WOTS outer-loop step preserves the outer-loop index binding `"i"`. -/
theorem wotsOuterStep_preserves_i_lookup (st : RuntimeState) :
    lookupValue (wotsOuterStep st).bindings "i" =
      lookupValue st.bindings "i" :=
  wotsOuterBody_preserves_i_lookup st (wotsOuterStep st) (wotsOuterStepLemma st)

/-- The 43-step WOTS outer fold preserves seed cell `0x00`. -/
theorem wotsOuterFold_preserves_memory_zero (st : RuntimeState) :
    ((foldLoop "i" wotsOuterStep
        { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
        0 (wordNormalize 43)).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "i" wotsOuterStep 0x00
    (fun i => i < 43)
    (fun s i hi => by
      have hI :
          lookupValue ({ s with bindings := bindValue s.bindings "i" (wordNormalize i) }).bindings
              "i" =
            wordNormalize i := by
        exact MemoryKit.lookupValue_bindValue_self s.bindings "i" (wordNormalize i)
      exact wotsOuterStep_preserves_memory_zero_of_i
        { s with bindings := bindValue s.bindings "i" (wordNormalize i) } i hi hI)
    { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
    0 (wordNormalize 43)
    (fun i _ hi => by simpa using hi)]

/-- One WOTS public-key copy step preserves seed cell `0x00` for the actual C13
loop-index range. -/
theorem copyStep_preserves_memory_zero_of_i
    (st : RuntimeState) (i : Nat)
    (hi : i < 43)
    (hI : lookupValue st.bindings "i" = wordNormalize i) :
    ((copyStep st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  have hINorm : wordNormalize i = i :=
    SegmentS2.wordNormalize_of_lt (lt_trans hi (by decide : 43 < 2 ^ 256))
  have hIeval : evalExpr [] st (v "i") = some i := by
    change some (lookupValue st.bindings "i") = some i
    rw [hI, hINorm]
  have hShiftBound : i <<< 5 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have : i * 2 ^ 5 < 43 * 2 ^ 5 := by
      exact Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 2 ^ 5)
    exact lt_trans this (by decide : 43 * 2 ^ 5 < 2 ^ 256)
  have hShift :
      evalExpr [] st (shlE (u 5) (v "i")) = some (i <<< 5) := by
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (u 5) (v "i") 5 i rfl hIeval
      (by decide : 5 < 2 ^ 256)
      (lt_trans hi (by decide : 43 < 2 ^ 256))
      hShiftBound
  have hOff :
      evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
        some (0x40 + (i <<< 5)) := by
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st (u 0x40) (shlE (u 5) (v "i")) 0x40 (i <<< 5)
      rfl hShift (by decide : 0x40 < 2 ^ 256) hShiftBound
      (by
        rw [Nat.shiftLeft_eq]
        have : 0x40 + i * 2 ^ 5 < 0x40 + 43 * 2 ^ 5 := by omega
        exact lt_trans this (by decide : 0x40 + 43 * 2 ^ 5 < 2 ^ 256))
  unfold copyStep copyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ (0x40 + (i <<< 5)) _ hOff rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ (0x40 + (i <<< 5)) 0x00 _ (by omega)]

/-- The 43-step WOTS public-key copy fold preserves seed cell `0x00`. -/
theorem copyFold_preserves_memory_zero (st : RuntimeState) :
    ((foldLoop "i" copyStep
        { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
        0 (wordNormalize 43)).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "i" copyStep 0x00
    (fun i => i < 43)
    (fun s i hi => by
      have hI :
          lookupValue ({ s with bindings := bindValue s.bindings "i" (wordNormalize i) }).bindings
              "i" =
            wordNormalize i := by
        exact MemoryKit.lookupValue_bindValue_self s.bindings "i" (wordNormalize i)
      exact copyStep_preserves_memory_zero_of_i
        { s with bindings := bindValue s.bindings "i" (wordNormalize i) } i hi hI)
    { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
    0 (wordNormalize 43)
    (fun i _ hi => by simpa using hi)]

/-! ## 3. The Layer-3 body reconstruction (Model.lean:154-203), split around the
checksum-guard `ite` as `prefix11 ++ (ite :: suffix14)`. -/

/-- Statements 154-163 + the digit-sum loop (everything before the guard). -/
def prefix11 : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  , mstore 0x40 (v "currentNode")
  , mstore 0x60 (v "count")
  , .letVar "d" (keccak 0x00 0x80)
  , .letVar "digitSum" (u 0)
  , .forEach "ii" (u 43) digitSumBody ]

/-- The straight-line part of `prefix11` before the checksum accumulation loop. -/
def prefixBeforeDigitLoop : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  , mstore 0x40 (v "currentNode")
  , mstore 0x60 (v "count")
  , .letVar "d" (keccak 0x00 0x80)
  , .letVar "digitSum" (u 0) ]

def beforeDigitLoop (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefixBeforeDigitLoop with | .continue s' => s' | _ => ls

def prefixBeforeDigest : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  , mstore 0x40 (v "currentNode")
  , mstore 0x60 (v "count") ]

def beforeDigest (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefixBeforeDigest with | .continue s' => s' | _ => ls

def afterDigitFold (ls : RuntimeState) : RuntimeState :=
  foldLoop "ii" digitSumStep
    { beforeDigitLoop ls with
      bindings := bindValue (beforeDigitLoop ls).bindings "ii" (wordNormalize 0) }
    0 (wordNormalize 43)

/-- The executable checksum fold preserves every binding except the accumulator. -/
theorem afterDigitFold_preserves_lookup_of_ne
    (ls : RuntimeState) (key : String) (hne : "ii" ≠ key) (hneDigit : key ≠ "digitSum") :
    lookupValue (afterDigitFold ls).bindings key =
      lookupValue (beforeDigitLoop ls).bindings key := by
  unfold afterDigitFold
  rw [ClimbLoop.foldLoop_preserves_lookup "ii" key digitSumStep hne
    (fun s => digitSumStep_preserves_lookup_of_ne s key hneDigit)]
  exact MemoryKit.lookupValue_bindValue_ne _ "ii" key _ hne

/-- The executable checksum fold only changes bindings, so it preserves scratch
cell `0x00` from the state before the fold. -/
theorem afterDigitFold_preserves_memory_zero (ls : RuntimeState) :
    ((afterDigitFold ls).world.memory 0x00).val =
      ((beforeDigitLoop ls).world.memory 0x00).val := by
  unfold afterDigitFold
  rw [ClimbLoop.foldLoop_preserves_memory_val "ii" digitSumStep 0 (by
    intro s
    unfold digitSumStep digitSumBody addE andE shrE mulE v u
    rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue s "digitSum" _ _ rfl)]
    rfl)]

/-- Statements 168-203 (everything after the guard). -/
def suffix14 : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs")
  , .forEach "i" (u 43) copyBody
  , .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK))
  , .letVar "authOff" (addE (v "countOff") (u 4))
  , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
  , .letVar "merkleNode" (v "wotsPk")
  , .letVar "mIdx" (v "idxLeaf")
  , .letVar "merklePtr" (addE (v "sigBase") (v "authOff"))
  , .forEach "h" (u 11) (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")
  , .assignVar "currentNode" (v "merkleNode")
  , .assignVar "sigOff" (addE (v "authOff") (u 176)) ]

/-- The straight-line suffix prefix before `authOff := countOff + 4`. -/
def suffixBeforeAuthOff : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs")
  , .forEach "i" (u 43) copyBody
  , .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK)) ]

/-- The straight-line part of `suffix14` before the XMSS Merkle-climb loop.
This state carries the concrete WOTS public-key word and the initialized
`merkleNode`/`mIdx`/`treeAdrs`/`merklePtr` cells consumed by the generic
Merkle-climb frame lemmas. -/
def suffixBeforeMerkle : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs")
  , .forEach "i" (u 43) copyBody
  , .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK))
  , .letVar "authOff" (addE (v "countOff") (u 4))
  , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
  , .letVar "merkleNode" (v "wotsPk")
  , .letVar "mIdx" (v "idxLeaf")
  , .letVar "merklePtr" (addE (v "sigBase") (v "authOff")) ]

def layerBody : List Stmt := prefix11 ++ (.ite condE revert0 [] :: suffix14)

def layerStmt : Stmt := .forEach "layer" (u 2) layerBody

set_option maxHeartbeats 8000000 in
/-- Faithfulness: `layerStmt` is *exactly* statement 25 of `c13VerifyBody`
(loop header, full body, every inner `forEach` and the checksum-guard `ite`). -/
theorem layerStmt_eq_slice :
    [layerStmt] = (c13VerifyBody.drop 25).take 1 := rfl

/-- One-step unfold of `execStmtList` on a cons, kept generic so the head
`execStmt` stays symbolic (no reduction of concrete loop-states). -/
private theorem execStmtList_cons_eq (st : RuntimeState) (s : Stmt) (rest : List Stmt) :
    execStmtList [] st (s :: rest) =
      (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) := by
  show (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) = _
  rfl

/-! ## 4. Threading the guard-free prefix and suffix. -/

/-- The state after running `prefix11` (always continues). -/
def afterDigit (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefix11 with | .continue s' => s' | _ => ls

/-- The named pre-checksum prefix always continues to `beforeDigitLoop`. -/
theorem beforeDigitLoop_eq (ls : RuntimeState) :
    execStmtList [] ls prefixBeforeDigitLoop = .continue (beforeDigitLoop ls) := by
  unfold beforeDigitLoop prefixBeforeDigitLoop mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  rfl

/-- The pre-checksum prefix does not rebind `"sigBase"`. -/
theorem beforeDigitLoop_preserves_sigBase (ls : RuntimeState) :
    lookupValue (beforeDigitLoop ls).bindings "sigBase" =
      lookupValue ls.bindings "sigBase" := by
  refine execStmtList_preserves_lookup "sigBase" prefixBeforeDigitLoop
    ls (beforeDigitLoop ls) ?_ (beforeDigitLoop_eq ls)
  intro s s'' stmt hmem hexec
  simp [prefixBeforeDigitLoop, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "idxLeaf" "sigBase" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "idxTree" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsAdrs" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "countOff" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "count" "sigBase" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact execStmt_letVar_preserves_lookup _ _ "d" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "digitSum" "sigBase" _ (by decide) hexec

/-- The pre-checksum prefix binds `"countOff"` to the incoming `"sigOff" + 688`. -/
theorem beforeDigitLoop_countOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256) :
    lookupValue (beforeDigitLoop ls).bindings "countOff" = sigOff + 688 := by
  unfold beforeDigitLoop prefixBeforeDigitLoop mstore u addE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ (by
    refine SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      _ (v "sigOff") (u 688) sigOff 688 ?_ rfl
      hSigOffLt (by decide : 688 < 2 ^ 256) hCountOffLt
    change some (lookupValue _ "sigOff") = some sigOff
    rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "sigOff" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "sigOff" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "sigOff" _ (by decide)]
    rw [hSigOff]))]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" "countOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "d" "countOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "countOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]

/-- The straight-line WOTS digest setup always continues to `beforeDigest`. -/
theorem beforeDigest_eq (ls : RuntimeState) :
    execStmtList [] ls prefixBeforeDigest = .continue (beforeDigest ls) := by
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- The pre-digest WOTS prefix never writes scratch cell `0x00`; it only writes
`0x20`, `0x40`, and `0x60`. -/
theorem beforeDigest_preserves_memory_zero (ls : RuntimeState) :
    ((beforeDigest ls).world.memory 0x00).val = (ls.world.memory 0x00).val := by
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
      MemoryKit.memUpdate_diff _ _ _ _ (by decide),
      MemoryKit.memUpdate_diff _ _ _ _ (by decide)]

/-- The straight-line WOTS prefix before the checksum loop preserves scratch
cell `0x00`; it only writes `0x20`, `0x40`, and `0x60`. -/
theorem beforeDigitLoop_preserves_memory_zero (ls : RuntimeState) :
    ((beforeDigitLoop ls).world.memory 0x00).val = (ls.world.memory 0x00).val := by
  unfold beforeDigitLoop prefixBeforeDigitLoop mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
      MemoryKit.memUpdate_diff _ _ _ _ (by decide),
      MemoryKit.memUpdate_diff _ _ _ _ (by decide)]

/-- The pre-digest WOTS prefix splits the low 11 bits of the incoming
`"idxTree"` binding into `"idxLeaf"`. -/
theorem beforeDigest_idxLeaf_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeDigest ls).bindings "idxLeaf" = idxTree % 2048 := by
  unfold beforeDigest prefixBeforeDigest mstore u andE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  change (evalExpr [] ls (andE (v "idxTree") (u 0x7FF))).getD 0 = idxTree % 2048
  have hAnd :
      evalExpr [] ls (andE (v "idxTree") (u 0x7FF)) =
        some (idxTree % 2048) := by
    have hLocal : evalExpr [] ls (v "idxTree") = some idxTree := by
      change some (lookupValue ls.bindings "idxTree") = some idxTree
      rw [hIdxTree]
    have hRaw :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
        ls (v "idxTree") idxTree 0x7FF hLocal hIdxTreeLt
        (by decide : 0x7FF < 2 ^ 256)
    simpa [andE, u, nat_land_low11] using hRaw
  rw [hAnd]
  rfl

/-- The pre-digest WOTS prefix shifts the incoming `"idxTree"` binding by the
C13 subtree height for the layer address. -/
theorem beforeDigest_idxTree_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeDigest ls).bindings "idxTree" = idxTree / 2048 := by
  unfold beforeDigest prefixBeforeDigest mstore u shrE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  change (evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (shrE (u 11) (v "idxTree"))).getD 0 = idxTree / 2048
  have hLit : evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (u 11) = some 11 := by
    rfl
  have hLocal : evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (v "idxTree") = some idxTree := by
    change some (lookupValue
        (bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0))
        "idxTree") = some idxTree
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "idxTree" _ (by decide)]
    rw [hIdxTree]
  have hShr :
      evalExpr []
        { ls with
          bindings := bindValue ls.bindings "idxLeaf"
            ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
        (shrE (u 11) (v "idxTree")) = some (idxTree >>> 11) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      _ (u 11) (v "idxTree") 11 idxTree hLit hLocal
      (by decide : 11 < 2 ^ 256) hIdxTreeLt
  rw [hShr]
  rw [Nat.shiftRight_eq_div_pow]
  rfl

/-- The longer pre-checksum prefix has the same shifted `"idxTree"` binding as
the pre-digest prefix; the extra statements only bind `"d"` and `"digitSum"`. -/
theorem beforeDigitLoop_idxTree_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeDigitLoop ls).bindings "idxTree" = idxTree / 2048 := by
  unfold beforeDigitLoop prefixBeforeDigitLoop mstore u shrE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "d" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  change (evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (shrE (u 11) (v "idxTree"))).getD 0 = idxTree / 2048
  have hLit : evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (u 11) = some 11 := by
    rfl
  have hLocal : evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (v "idxTree") = some idxTree := by
    change some (lookupValue
        (bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0))
        "idxTree") = some idxTree
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "idxTree" _ (by decide)]
    rw [hIdxTree]
  have hShr :
      evalExpr []
        { ls with
          bindings := bindValue ls.bindings "idxLeaf"
            ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
        (shrE (u 11) (v "idxTree")) = some (idxTree >>> 11) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      _ (u 11) (v "idxTree") 11 idxTree hLit hLocal
      (by decide : 11 < 2 ^ 256) hIdxTreeLt
  rw [hShr]
  rw [Nat.shiftRight_eq_div_pow]
  rfl

/-- The pre-digest WOTS prefix assembles the WOTS hash-base address from the
layer and the split C13 hypertree index. -/
theorem beforeDigest_wotsAdrs_eq_of_layer_idxTree
    (ls : RuntimeState) (layer idxTree : Nat)
    (hLayer : lookupValue ls.bindings "layer" = layer)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 22) :
    lookupValue (beforeDigest ls).bindings "wotsAdrs" =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase
        layer (idxTree / 2048) (idxTree % 2048) := by
  unfold beforeDigest prefixBeforeDigest mstore u andE shrE shlE orE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  let idxLeafVal :=
    (evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0
  let st1 : RuntimeState := { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
  let idxTreeVal := (evalExpr [] st1 (.shr (.literal 11) (.localVar "idxTree"))).getD 0
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "idxTree" idxTreeVal }
  change (evalExpr [] st2
      (.bitOr (.shl (.literal 224) (.localVar "layer"))
        (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
          (.shl (.literal 64) (.localVar "idxLeaf"))))).getD 0 =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase
        layer (idxTree / 2048) (idxTree % 2048)
  have hIdxLeafVal : idxLeafVal = idxTree % 2048 := by
    unfold idxLeafVal
    have hLocal : evalExpr [] ls (.localVar "idxTree") = some idxTree := by
      change some (lookupValue ls.bindings "idxTree") = some idxTree
      rw [hIdxTree]
    have hRaw :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
        ls (.localVar "idxTree") idxTree 0x7FF hLocal
        (lt_trans hIdxTreeLt (by decide : 2 ^ 22 < 2 ^ 256))
        (by decide : 0x7FF < 2 ^ 256)
    rw [hRaw]
    simp [nat_land_low11]
  have hIdxTreeVal : idxTreeVal = idxTree / 2048 := by
    unfold idxTreeVal st1
    have hLit : evalExpr []
        { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
        (.literal 11) = some 11 := by
      rfl
    have hLocal : evalExpr []
        { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
        (.localVar "idxTree") = some idxTree := by
      change some (lookupValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree")
        = some idxTree
      rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "idxTree" _ (by decide)]
      rw [hIdxTree]
    have hShr :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
        { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
        (.literal 11) (.localVar "idxTree") 11 idxTree hLit hLocal
        (by decide : 11 < 2 ^ 256)
        (lt_trans hIdxTreeLt (by decide : 2 ^ 22 < 2 ^ 256))
    rw [hShr, Nat.shiftRight_eq_div_pow]
    norm_num
  have hLayerEval : evalExpr [] st2 (.localVar "layer") = some layer := by
    unfold st2 st1
    change some (lookupValue
        (bindValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree" idxTreeVal)
        "layer") = some layer
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "layer" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "layer" _ (by decide)]
    rw [hLayer]
  have hIdxTreeEval : evalExpr [] st2 (.localVar "idxTree") = some (idxTree / 2048) := by
    unfold st2
    change some (lookupValue (bindValue st1.bindings "idxTree" idxTreeVal) "idxTree")
      = some (idxTree / 2048)
    rw [MemoryKit.lookupValue_bindValue_self]
    exact congrArg some hIdxTreeVal
  have hIdxLeafEval : evalExpr [] st2 (.localVar "idxLeaf") = some (idxTree % 2048) := by
    unfold st2 st1
    change some (lookupValue
        (bindValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree" idxTreeVal)
        "idxLeaf") = some (idxTree % 2048)
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "idxLeaf" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_self]
    exact congrArg some hIdxLeafVal
  have h224 :
      evalExpr [] st2 (.shl (.literal 224) (.localVar "layer")) =
        some (layer <<< 224) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st2 (.literal 224) (.localVar "layer") 224 layer rfl hLayerEval
      (by decide : 224 < 2 ^ 256)
      (lt_trans hLayerLt (by decide : 2 ^ 32 < 2 ^ 256))
      (by
        rw [Nat.shiftLeft_eq]
        calc
          layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
            Nat.mul_lt_mul_of_pos_right hLayerLt (by decide)
          _ = 2 ^ 256 := by norm_num [Nat.pow_add])
  have h128 :
      evalExpr [] st2 (.shl (.literal 128) (.localVar "idxTree")) =
        some ((idxTree / 2048) <<< 128) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st2 (.literal 128) (.localVar "idxTree") 128 (idxTree / 2048) rfl hIdxTreeEval
      (by decide : 128 < 2 ^ 256)
      (lt_trans (Nat.div_lt_of_lt_mul hIdxTreeLt) (by decide : 2048 < 2 ^ 256))
      (by
        have hnext : idxTree / 2048 < 2 ^ 11 := by
          exact Nat.div_lt_of_lt_mul hIdxTreeLt
        rw [Nat.shiftLeft_eq]
        calc
          (idxTree / 2048) * 2 ^ 128 < 2 ^ 11 * 2 ^ 128 :=
            Nat.mul_lt_mul_of_pos_right hnext (by decide)
          _ < 2 ^ 256 := by decide)
  have h64 :
      evalExpr [] st2 (.shl (.literal 64) (.localVar "idxLeaf")) =
        some ((idxTree % 2048) <<< 64) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st2 (.literal 64) (.localVar "idxLeaf") 64 (idxTree % 2048) rfl hIdxLeafEval
      (by decide : 64 < 2 ^ 256)
      (lt_trans (Nat.mod_lt _ (by decide : 0 < 2048)) (by decide : 2048 < 2 ^ 256))
      (by
        have hleaf : idxTree % 2048 < 2048 := Nat.mod_lt _ (by decide : 0 < 2048)
        rw [Nat.shiftLeft_eq]
        calc
          (idxTree % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
            Nat.mul_lt_mul_of_pos_right hleaf (by decide)
          _ < 2 ^ 256 := by decide)
  have h224lt : layer <<< 224 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right hLayerLt (by decide)
      _ = 2 ^ 256 := by norm_num [Nat.pow_add]
  have h128lt : (idxTree / 2048) <<< 128 < 2 ^ 256 := by
    have hnext : idxTree / 2048 < 2 ^ 11 := Nat.div_lt_of_lt_mul hIdxTreeLt
    rw [Nat.shiftLeft_eq]
    calc
      (idxTree / 2048) * 2 ^ 128 < 2 ^ 11 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hnext (by decide)
      _ < 2 ^ 256 := by decide
  have h64lt : (idxTree % 2048) <<< 64 < 2 ^ 256 := by
    have hleaf : idxTree % 2048 < 2048 := Nat.mod_lt _ (by decide : 0 < 2048)
    rw [Nat.shiftLeft_eq]
    calc
      (idxTree % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hleaf (by decide)
      _ < 2 ^ 256 := by decide
  have hinner :
      evalExpr [] st2
        (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
          (.shl (.literal 64) (.localVar "idxLeaf"))) =
        some (((idxTree / 2048) <<< 128) ||| ((idxTree % 2048) <<< 64)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st2 (.shl (.literal 128) (.localVar "idxTree"))
      (.shl (.literal 64) (.localVar "idxLeaf"))
      ((idxTree / 2048) <<< 128) ((idxTree % 2048) <<< 64)
      h128 h64 h128lt h64lt
  have hinnerLt :
      (((idxTree / 2048) <<< 128) ||| ((idxTree % 2048) <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128lt h64lt
  have hfull :
      evalExpr [] st2
        (.bitOr (.shl (.literal 224) (.localVar "layer"))
          (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
            (.shl (.literal 64) (.localVar "idxLeaf")))) =
        some ((layer <<< 224) |||
          (((idxTree / 2048) <<< 128) ||| ((idxTree % 2048) <<< 64))) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st2 (.shl (.literal 224) (.localVar "layer"))
      (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
        (.shl (.literal 64) (.localVar "idxLeaf")))
      (layer <<< 224)
      (((idxTree / 2048) <<< 128) ||| ((idxTree % 2048) <<< 64))
      h224 hinner h224lt hinnerLt
  rw [hfull]
  simp [SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase, Nat.lor_assoc]

/-- The pre-digest WOTS prefix binds `"count"` to the high 32 bits of the
signature calldata word at `sigBase + sigOff + 688`. -/
theorem beforeDigest_count_eq_of_sigBase_sigOff_calldata
    (ls : RuntimeState) (sigBase sigOff : Nat) (calldata : List Nat)
    (hSigBase : lookupValue ls.bindings "sigBase" = sigBase)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSelector : ls.selector = 0)
    (hCalldata : ls.world.calldata = calldata)
    (hSigBaseLt : sigBase < 2 ^ 256)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hOffsetLt : sigBase + (sigOff + 688) < 2 ^ 256) :
    lookupValue (beforeDigest ls).bindings "count" =
      (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
        (sigBase + (sigOff + 688))) >>> 224 := by
  unfold beforeDigest prefixBeforeDigest mstore u andE shrE shlE orE v addE cdload
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_self]
  let idxLeafVal :=
    (evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0
  let st1 : RuntimeState := { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
  let idxTreeVal := (evalExpr [] st1 (.shr (.literal 11) (.localVar "idxTree"))).getD 0
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "idxTree" idxTreeVal }
  let wotsAdrsVal :=
    (evalExpr [] st2
      (.bitOr (.shl (.literal 224) (.localVar "layer"))
        (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
          (.shl (.literal 64) (.localVar "idxLeaf"))))).getD 0
  let st3 : RuntimeState := { st2 with bindings := bindValue st2.bindings "wotsAdrs" wotsAdrsVal }
  let countOffVal := (evalExpr [] st3 (.add (.localVar "sigOff") (.literal 688))).getD 0
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "countOff" countOffVal }
  change (evalExpr [] st4
      (.shr (.literal 224)
        (.calldataload (.add (.localVar "sigBase") (.localVar "countOff"))))).getD 0 =
      (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
        (sigBase + (sigOff + 688))) >>> 224
  have hSigOffEval : evalExpr [] st3 (.localVar "sigOff") = some sigOff := by
    unfold st3 st2 st1
    change some (lookupValue
        (bindValue
          (bindValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree" idxTreeVal)
          "wotsAdrs" wotsAdrsVal)
        "sigOff") = some sigOff
    rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "sigOff" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "sigOff" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "sigOff" _ (by decide)]
    rw [hSigOff]
  have h688 : evalExpr [] st3 (.literal 688) = some 688 := by
    show some (wordNormalize 688) = some 688
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 688 < 2 ^ 256)]
  have hCountOffEval :
      evalExpr [] st3 (.add (.localVar "sigOff") (.literal 688)) =
        some (sigOff + 688) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st3 (.localVar "sigOff") (.literal 688) sigOff 688
      hSigOffEval h688 hSigOffLt (by decide : 688 < 2 ^ 256) hCountOffLt
  have hCountOffVal : countOffVal = sigOff + 688 := by
    unfold countOffVal
    rw [hCountOffEval]
    rfl
  have hSigBaseEval : evalExpr [] st4 (.localVar "sigBase") = some sigBase := by
    unfold st4 st3 st2 st1
    change some (lookupValue
        (bindValue
          (bindValue
            (bindValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree" idxTreeVal)
            "wotsAdrs" wotsAdrsVal)
          "countOff" countOffVal)
        "sigBase") = some sigBase
    rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "sigBase" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "sigBase" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "sigBase" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "sigBase" _ (by decide)]
    rw [hSigBase]
  have hCountOffEval4 : evalExpr [] st4 (.localVar "countOff") =
      some (sigOff + 688) := by
    unfold st4
    change some (lookupValue (bindValue st3.bindings "countOff" countOffVal) "countOff")
      = some (sigOff + 688)
    rw [MemoryKit.lookupValue_bindValue_self]
    exact congrArg some hCountOffVal
  have hOffset :
      evalExpr [] st4 (.add (.localVar "sigBase") (.localVar "countOff")) =
        some (sigBase + (sigOff + 688)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st4 (.localVar "sigBase") (.localVar "countOff") sigBase (sigOff + 688)
      hSigBaseEval hCountOffEval4 hSigBaseLt hCountOffLt hOffsetLt
  have hLoad :
      evalExpr [] st4 (.calldataload (.add (.localVar "sigBase") (.localVar "countOff"))) =
        some (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
          (sigBase + (sigOff + 688))) := by
    change (do
        let resolvedOffset ←
          evalExpr [] st4 (.add (.localVar "sigBase") (.localVar "countOff"))
        some (Compiler.Proofs.YulGeneration.calldataloadWord st4.selector
          st4.world.calldata resolvedOffset)) =
      some (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
        (sigBase + (sigOff + 688)))
    rw [hOffset]
    unfold st4 st3 st2 st1
    rw [hSelector, hCalldata]
    rfl
  have hLoadLt :
      Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
          (sigBase + (sigOff + 688)) < 2 ^ 256 := by
    by_cases hsmall : sigBase + (sigOff + 688) < 4
    · simp [Compiler.Proofs.YulGeneration.calldataloadWord, hsmall]
    · simp [Compiler.Proofs.YulGeneration.calldataloadWord, hsmall,
        Compiler.Constants.evmModulus]
      split <;> exact Nat.mod_lt _ (by decide : 0 < 2 ^ 256)
  have h224 : evalExpr [] st4 (.literal 224) = some 224 := by
    show some (wordNormalize 224) = some 224
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 224 < 2 ^ 256)]
  have hShr :
      evalExpr [] st4
        (.shr (.literal 224)
          (.calldataload (.add (.localVar "sigBase") (.localVar "countOff")))) =
        some ((Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
          (sigBase + (sigOff + 688))) >>> 224) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      st4 (.literal 224)
      (.calldataload (.add (.localVar "sigBase") (.localVar "countOff")))
      224
      (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
        (sigBase + (sigOff + 688)))
      h224 hLoad (by decide : 224 < 2 ^ 256) hLoadLt
  rw [hShr]
  rfl

/-- If the named WOTS address binding has been identified, the pre-digest
scratch cell `0x20` contains that word. -/
theorem beforeDigest_memory_0x20_eq_of_wotsAdrs
    (ls : RuntimeState) (wotsAdrs : Nat)
    (hWotsAdrs : lookupValue (beforeDigest ls).bindings "wotsAdrs" = wotsAdrs) :
    ((beforeDigest ls).world.memory 0x20).val = wordNormalize wotsAdrs := by
  rw [← hWotsAdrs]
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
  change (MemoryKit.memUpdate _ (wordNormalize 32) _ (wordNormalize 32)).val =
    wordNormalize (lookupValue _ "wotsAdrs")
  rw [MemoryKit.memUpdate_val_same]

/-- The pre-digest WOTS prefix writes scratch cell `0x40` from the incoming
`"currentNode"` binding. -/
theorem beforeDigest_memory_0x40_eq_currentNode (ls : RuntimeState) :
    ((beforeDigest ls).world.memory 0x40).val =
      wordNormalize (lookupValue ls.bindings "currentNode") := by
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
  change (MemoryKit.memUpdate _ (wordNormalize 64) _ (wordNormalize 64)).val =
    wordNormalize (lookupValue ls.bindings "currentNode")
  rw [MemoryKit.memUpdate_val_same]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "currentNode" _ (by decide)]

/-- Word-shaped specialization of `beforeDigest_memory_0x40_eq_currentNode`. -/
theorem beforeDigest_memory_0x40_eq_wordOfHash16
    (ls : RuntimeState) (node : ByteArray)
    (hCurrent : lookupValue ls.bindings "currentNode" =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node) :
    ((beforeDigest ls).world.memory 0x40).val =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node := by
  rw [beforeDigest_memory_0x40_eq_currentNode, hCurrent]
  exact SegmentS2.wordNormalize_of_lt (SegmentS2.wordOfHash16_lt node)

/-- If the named WOTS count binding has been identified, the pre-digest scratch
cell `0x60` contains that word. -/
theorem beforeDigest_memory_0x60_eq_of_count
    (ls : RuntimeState) (count : Nat)
    (hCount : lookupValue (beforeDigest ls).bindings "count" = count) :
    ((beforeDigest ls).world.memory 0x60).val = wordNormalize count := by
  rw [← hCount]
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  change (MemoryKit.memUpdate _ (wordNormalize 96) _ (wordNormalize 96)).val =
    wordNormalize (lookupValue _ "count")
  rw [MemoryKit.memUpdate_val_same]

/-- The pre-checksum prefix binds `"d"` to the Keccak word over the four C13 WOTS
digest scratch cells.  Cell `0` is prepared by earlier segments; this prefix
writes `0x20`, `0x40`, and `0x60` before hashing `0x00..0x80`. -/
theorem beforeDigitLoop_d_eq_keccakWords (ls : RuntimeState) :
    lookupValue (beforeDigitLoop ls).bindings "d" =
      SphincsMinusVerifierSpec.C13Concrete.keccakWords
        [ ((beforeDigest ls).world.memory 0x00).val
        , ((beforeDigest ls).world.memory 0x20).val
        , ((beforeDigest ls).world.memory 0x40).val
        , ((beforeDigest ls).world.memory 0x60).val ] := by
  unfold beforeDigitLoop
  rw [show prefixBeforeDigitLoop = prefixBeforeDigest ++
      [.letVar "d" (keccak 0x00 0x80), .letVar "digitSum" (u 0)] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeDigest_eq ls)]
  unfold beforeDigest
  rw [beforeDigest_eq ls]
  simp only
  unfold keccak u
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue _ "d" _ _
      (SphincsMinusVerifiers.KeccakBridge.evalExpr_keccak256_eq_keccakWords
        _ 0x00 0x80
        [ ((beforeDigest ls).world.memory 0x00).val
        , ((beforeDigest ls).world.memory 0x20).val
        , ((beforeDigest ls).world.memory 0x40).val
        , ((beforeDigest ls).world.memory 0x60).val ]
        rfl rfl (by
          intro i hi
          rcases i with _ | i
          · simp
          rcases i with _ | i
          · simp
          rcases i with _ | i
          · simp
          rcases i with _ | i
          · simp
          · simp at hi
            omega)))]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" "d" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]

/-- WOTS-digest specialization of `beforeDigitLoop_d_eq_keccakWords` once the
four scratch cells have been identified. -/
theorem beforeDigitLoop_d_eq_wotsDigest_of_scratch
    (ls : RuntimeState) (seed layer idxTree idxLeaf count node : Nat)
    (hSeed : ((beforeDigest ls).world.memory 0x00).val = seed)
    (hAdrs :
      ((beforeDigest ls).world.memory 0x20).val =
        SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer idxTree idxLeaf)
    (hNode : ((beforeDigest ls).world.memory 0x40).val = node)
    (hCount : ((beforeDigest ls).world.memory 0x60).val = count) :
    lookupValue (beforeDigitLoop ls).bindings "d" =
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest
        seed layer idxTree idxLeaf count node := by
  rw [beforeDigitLoop_d_eq_keccakWords]
  rw [hSeed, hAdrs, hNode, hCount]
  rfl

theorem afterDigit_eq (ls : RuntimeState) :
    execStmtList [] ls prefix11 = .continue (afterDigit ls) := by
  unfold afterDigit prefix11 mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "ii" (.literal 43) digitSumBody _ _ digitSumStep rfl digitSumStepLemma)]
  rfl

/-- The checksum prefix only updates bindings and scratch memory; it preserves
the ABI selector and calldata image. -/
theorem afterDigit_preserves_selector_calldata (ls : RuntimeState) :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata ls (afterDigit ls) := by
  refine SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    prefix11 ls (afterDigit ls) ?_ (afterDigit_eq ls)
  intro s s'' stmt hmem hexec
  simp [prefix11, mstore] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "idxLeaf" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' "idxTree" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "wotsAdrs" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "countOff" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "count" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "d" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "digitSum" _ hexec
  · subst h
    refine SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "ii" (u 43) digitSumBody s s'' ?_ hexec
    intro t t'' stmt' hmem' hexec'
    simp [digitSumBody] at hmem'
    subst hmem'
    exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      t t'' "digitSum" _ hexec'

/-- Frame obligation for statement bodies that preserve selector/calldata. -/
abbrev PreservesSelectorCalldataBody (body : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ body → execStmt [] s stmt = .continue s'' →
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata s s''

theorem digitSumBody_preserves_selector_calldata :
    PreservesSelectorCalldataBody digitSumBody := by
  intro s s'' stmt hmem hexec
  simp [digitSumBody] at hmem
  subst hmem
  exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
    s s'' "digitSum" _ hexec

theorem wotsChainBody_preserves_selector_calldata :
    PreservesSelectorCalldataBody wotsChainBody := by
  intro s s'' stmt hmem hexec
  simp [wotsChainBody] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' "val" _ hexec

theorem copyBody_preserves_selector_calldata :
    PreservesSelectorCalldataBody copyBody := by
  intro s s'' stmt hmem hexec
  simp [copyBody] at hmem
  subst hmem
  exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
    s s'' _ _ hexec

theorem merkleClimbBody_preserves_selector_calldata
    (nodeVar idxVar adrsBaseVar authPtrVar : String) :
    PreservesSelectorCalldataBody
      (merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar) := by
  intro s s'' stmt hmem hexec
  simp [merkleClimbBody] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "sibling" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "parentIdx" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "s" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' nodeVar _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' idxVar _ hexec

theorem wotsOuterBody_preserves_selector_calldata :
    PreservesSelectorCalldataBody wotsOuterBody := by
  intro s s'' stmt hmem hexec
  simp [wotsOuterBody] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "digit" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "steps" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "val" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "chainBase" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "step" _ wotsChainBody s s'' wotsChainBody_preserves_selector_calldata hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec

/-- The accepting layer suffix preserves selector/calldata. -/
theorem suffix14_preserves_selector_calldata :
    PreservesSelectorCalldataBody suffix14 := by
  intro s s'' stmt hmem hexec
  simp [suffix14, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "wotsPtr" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "i" _ wotsOuterBody s s'' wotsOuterBody_preserves_selector_calldata hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "pkAdrs" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "i" _ copyBody s s'' copyBody_preserves_selector_calldata hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "wotsPk" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "authOff" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "treeAdrs" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "merkleNode" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "mIdx" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "merklePtr" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "h" _ (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")
      s s'' (merkleClimbBody_preserves_selector_calldata
        "merkleNode" "mIdx" "treeAdrs" "merklePtr") hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' "currentNode" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' "sigOff" _ hexec

/-- The full checksum prefix continues to the named pure fold state. -/
theorem prefix11_eq_afterDigitFold (ls : RuntimeState) :
    execStmtList [] ls prefix11 = .continue (afterDigitFold ls) := by
  rw [show prefix11 = prefixBeforeDigitLoop ++
      [.forEach "ii" (u 43) digitSumBody] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeDigitLoop_eq ls)]
  unfold afterDigitFold
  unfold u
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "ii" (.literal 43) digitSumBody _ _ digitSumStep rfl digitSumStepLemma)]
  rfl

/-- `afterDigit` is definitionally the pure fold image of the executable checksum
loop once the straight-line prefix has been named. -/
theorem afterDigit_eq_afterDigitFold (ls : RuntimeState) :
    afterDigit ls = afterDigitFold ls := by
  unfold afterDigit
  rw [prefix11_eq_afterDigitFold ls]

/-- The full checksum prefix preserves scratch cell `0x00`. -/
theorem afterDigit_preserves_memory_zero (ls : RuntimeState) :
    ((afterDigit ls).world.memory 0x00).val = (ls.world.memory 0x00).val := by
  rw [afterDigit_eq_afterDigitFold]
  rw [afterDigitFold_preserves_memory_zero]
  exact beforeDigitLoop_preserves_memory_zero ls

/-- The executable checksum prefix and the named pure fold expose the same
`digitSum` binding. -/
theorem afterDigit_digitSum_eq_afterDigitFold (ls : RuntimeState) :
    lookupValue (afterDigit ls).bindings "digitSum" =
      lookupValue (afterDigitFold ls).bindings "digitSum" := by
  rw [afterDigit_eq_afterDigitFold ls]

/-- The executable checksum prefix preserves every non-loop, non-accumulator
binding from the named state immediately before the checksum fold. -/
theorem afterDigit_preserves_lookup_of_ne
    (ls : RuntimeState) (key : String) (hne : "ii" ≠ key)
    (hneDigit : key ≠ "digitSum") :
    lookupValue (afterDigit ls).bindings key =
      lookupValue (beforeDigitLoop ls).bindings key := by
  rw [afterDigit_eq_afterDigitFold ls]
  exact afterDigitFold_preserves_lookup_of_ne ls key hne hneDigit

private def digitSumPrefix (d : Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + ((d >>> (3 * i)) % 8)) 0

private theorem digitSumPrefix_le (d n : Nat) :
    digitSumPrefix d n ≤ 7 * n := by
  unfold digitSumPrefix
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hdigit : (d >>> (3 * n)) % 8 ≤ 7 := by
        exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 8))
      calc
        (List.range n).foldl (fun acc i => acc + (d >>> (3 * i)) % 8) 0
            + (d >>> (3 * n)) % 8
            ≤ 7 * n + 7 := Nat.add_le_add ih hdigit
        _ = 7 * (n + 1) := by ring

/-- The executable checksum fold computes the same 43-digit WOTS+C checksum as
`C13Concrete.wotsDigitSum`, for any state whose straight-line prefix has already
bound `"d"` and initialized `"digitSum"` to zero. -/
theorem afterDigitFold_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
    (ls : RuntimeState) (d : Nat)
    (hd : lookupValue (beforeDigitLoop ls).bindings "d" = d)
    (hdBound : d < 2 ^ 256) :
    lookupValue (afterDigitFold ls).bindings "digitSum" = wotsDigitSum d := by
  unfold afterDigitFold wotsDigitSum
  have h43 : wordNormalize 43 = 43 :=
    SegmentS2.wordNormalize_of_lt (by decide : 43 < 2 ^ 256)
  rw [h43]
  let init : RuntimeState :=
    { beforeDigitLoop ls with
      bindings := bindValue (beforeDigitLoop ls).bindings "ii" (wordNormalize 0) }
  have hInitAcc : lookupValue init.bindings "digitSum" = 0 := by
    unfold init
    rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "digitSum" _ (by decide)]
    unfold beforeDigitLoop prefixBeforeDigitLoop mstore u
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
    simp only [execStmtList]
    rw [MemoryKit.lookupValue_bindValue_self]
    rfl
  have hInitD : lookupValue init.bindings "d" = d := by
    unfold init
    rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "d" _ (by decide)]
    exact hd
  have h :
      ∀ n, n ≤ 43 →
        lookupValue (foldLoop "ii" digitSumStep init 0 n).bindings "digitSum"
          = digitSumPrefix d n ∧
        lookupValue (foldLoop "ii" digitSumStep init 0 n).bindings "d" = d := by
    intro n hn
    induction n with
    | zero =>
        simp [ClimbLoop.foldLoop_zero, digitSumPrefix, hInitAcc, hInitD]
    | succ n ih =>
        have hn' : n ≤ 43 := by omega
        rcases ih hn' with ⟨hAcc, hD⟩
        rw [show foldLoop "ii" digitSumStep init 0 (n + 1) =
            digitSumStep
              { foldLoop "ii" digitSumStep init 0 n with
                bindings := bindValue (foldLoop "ii" digitSumStep init 0 n).bindings
                  "ii" (wordNormalize n) } by
          rw [ClimbLoop.foldLoop_append "ii" digitSumStep init 0 n 1]
          simp [ClimbLoop.foldLoop_succ, ClimbLoop.foldLoop_zero]]
        have hi : n < 43 := by omega
        have hii :
            lookupValue
              (bindValue (foldLoop "ii" digitSumStep init 0 n).bindings "ii"
                (wordNormalize n)) "ii" = n := by
          rw [MemoryKit.lookupValue_bindValue_self]
          exact SegmentS2.wordNormalize_of_lt (lt_trans hi (by decide : 43 < 2 ^ 256))
        have hacc' :
            lookupValue
              (bindValue (foldLoop "ii" digitSumStep init 0 n).bindings "ii"
                (wordNormalize n)) "digitSum" = digitSumPrefix d n := by
          rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "digitSum" _ (by decide)]
          exact hAcc
        have hd' :
            lookupValue
              (bindValue (foldLoop "ii" digitSumStep init 0 n).bindings "ii"
                (wordNormalize n)) "d" = d := by
          rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "d" _ (by decide)]
          exact hD
        constructor
        · rw [digitSumStep_digitSum_eq_add_digit
            { (foldLoop "ii" digitSumStep init 0 n) with
              bindings := bindValue (foldLoop "ii" digitSumStep init 0 n).bindings
                "ii" (wordNormalize n) }
            n (digitSumPrefix d n) d hii hacc' hd' hi (digitSumPrefix_le d n) hdBound]
          unfold digitSumPrefix
          rw [List.range_succ, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
        · rw [digitSumStep_preserves_lookup_of_ne _ "d" (by decide)]
          exact hd'
  exact (h 43 (by rfl)).1

theorem afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
    (ls : RuntimeState) (d : Nat)
    (hd : lookupValue (beforeDigitLoop ls).bindings "d" = d)
    (hdBound : d < 2 ^ 256) :
    lookupValue (afterDigit ls).bindings "digitSum" = wotsDigitSum d := by
  rw [afterDigit_digitSum_eq_afterDigitFold]
  exact afterDigitFold_digitSum_eq_wotsDigitSum_of_beforeDigitLoop ls d hd hdBound

/-- The pure transformer for one accepting layer iteration: the `.continue`
payload of `suffix14` run from `afterDigit ls`. -/
def stepLayer (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffix14 with | .continue s' => s' | _ => afterDigit ls

/-- The state immediately before the XMSS Merkle-climb loop inside one accepting
layer iteration. -/
def beforeMerkle (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffixBeforeMerkle with
  | .continue s' => s'
  | _ => afterDigit ls

/-- The state immediately before binding `"authOff"`. -/
def beforeAuthOff (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffixBeforeAuthOff with
  | .continue s' => s'
  | _ => afterDigit ls

theorem beforeAuthOff_eq (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffixBeforeAuthOff = .continue (beforeAuthOff ls) := by
  unfold beforeAuthOff suffixBeforeAuthOff mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rfl

/-- The prefix before binding `"authOff"` preserves seed cell `0x00` once the two
loop statements are supplied as bounded frame facts. This keeps the straight-line
frame separate from the heavier WOTS/copy loop adapters. -/
theorem beforeAuthOff_preserves_memory_zero_of_loop_frames
    (ls : RuntimeState)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val) :
    ((beforeAuthOff ls).world.memory 0x00).val =
      ((afterDigit ls).world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 suffixBeforeAuthOff (afterDigit ls) (beforeAuthOff ls) ?_
    (beforeAuthOff_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeAuthOff, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsPtr" _ hexec
  · exact hWots s s'' hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "pkAdrs" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 _ _ ?_ hexec
    intro ro rv hoff _
    cases hoff
    decide
  · exact hCopy s s'' hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsPk" _ hexec

/-- The suffix prefix before `"authOff"` does not rebind `"countOff"`. -/
theorem suffixBeforeAuthOff_preserves_countOff (ls : RuntimeState) :
    lookupValue (beforeAuthOff ls).bindings "countOff" =
      lookupValue (afterDigit ls).bindings "countOff" := by
  refine execStmtList_preserves_lookup "countOff" suffixBeforeAuthOff
    (afterDigit ls) (beforeAuthOff ls) ?_ (beforeAuthOff_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeAuthOff, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "countOff" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "countOff" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "countOff" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "countOff" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody, mstoreE] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "countOff" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "countOff" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "countOff" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "countOff" _ (by decide) hexec

/-- The state before binding `"authOff"` still carries the count offset computed
from the incoming `"sigOff"`. -/
theorem beforeAuthOff_countOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256) :
    lookupValue (beforeAuthOff ls).bindings "countOff" = sigOff + 688 := by
  rw [suffixBeforeAuthOff_preserves_countOff]
  rw [afterDigit_preserves_lookup_of_ne ls "countOff" (by decide) (by decide)]
  exact beforeDigitLoop_countOff_eq_of_sigOff ls sigOff hSigOff hSigOffLt hCountOffLt

theorem beforeMerkle_eq (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffixBeforeMerkle = .continue (beforeMerkle ls) := by
  unfold beforeMerkle suffixBeforeMerkle mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  rfl

/-- The suffix leading to the Merkle loop does not rebind `"countOff"`. -/
theorem suffixBeforeMerkle_preserves_countOff (ls : RuntimeState) :
    lookupValue (beforeMerkle ls).bindings "countOff" =
      lookupValue (afterDigit ls).bindings "countOff" := by
  refine execStmtList_preserves_lookup "countOff" suffixBeforeMerkle
    (afterDigit ls) (beforeMerkle ls) ?_ (beforeMerkle_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeMerkle, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "countOff" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "countOff" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "countOff" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "countOff" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody, mstoreE] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "countOff" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "countOff" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "countOff" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "authOff" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "treeAdrs" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merkleNode" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "mIdx" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merklePtr" "countOff" _ (by decide) hexec

/-- The state before the Merkle loop still carries the count offset computed
from the incoming `"sigOff"`. -/
theorem beforeMerkle_countOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256) :
    lookupValue (beforeMerkle ls).bindings "countOff" = sigOff + 688 := by
  rw [suffixBeforeMerkle_preserves_countOff]
  rw [afterDigit_preserves_lookup_of_ne ls "countOff" (by decide) (by decide)]
  exact beforeDigitLoop_countOff_eq_of_sigOff ls sigOff hSigOff hSigOffLt hCountOffLt

/-- The state before the Merkle loop binds `"authOff"` to incoming
`"sigOff" + 692`. -/
theorem beforeMerkle_authOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hAuthOffLt : sigOff + 692 < 2 ^ 256) :
    lookupValue (beforeMerkle ls).bindings "authOff" = sigOff + 692 := by
  unfold beforeMerkle
  rw [show suffixBeforeMerkle =
      suffixBeforeAuthOff ++
        [ .letVar "authOff" (addE (v "countOff") (u 4))
        , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
        , .letVar "merkleNode" (v "wotsPk")
        , .letVar "mIdx" (v "idxLeaf")
        , .letVar "merklePtr" (addE (v "sigBase") (v "authOff")) ] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeAuthOff_eq ls)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_letVar_continue _ "authOff" _ (sigOff + 692) (by
    have hCountOff :
        evalExpr [] (beforeAuthOff ls) (v "countOff") = some (sigOff + 688) := by
      change some (lookupValue (beforeAuthOff ls).bindings "countOff") = some (sigOff + 688)
      rw [beforeAuthOff_countOff_eq_of_sigOff ls sigOff hSigOff hSigOffLt hCountOffLt]
    have hSum : sigOff + 688 + 4 = sigOff + 692 := by omega
    rw [← hSum]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      _ (v "countOff") (u 4) (sigOff + 688) 4 hCountOff rfl
      hCountOffLt (by decide : 4 < 2 ^ 256) (by simpa [hSum] using hAuthOffLt)))]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "treeAdrs" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]

/-- One XMSS Merkle-climb step does not rebind `"authOff"`. -/
theorem merkleStep_preserves_authOff (st : RuntimeState) :
    lookupValue
        (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" st).bindings
        "authOff" =
      lookupValue st.bindings "authOff" := by
  refine execStmtList_preserves_lookup "authOff"
    (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")
    st (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" st)
    ?_ (SphincsMinusVerifiers.ClimbKit.merkleClimbStep
      "merkleNode" "mIdx" "treeAdrs" "merklePtr" st)
  intro s s'' stmt hmem hexec
  simp [merkleClimbBody, mstoreE] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "sibling" "authOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "parentIdx" "authOff" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "authOff" _ _ hexec
  · exact execStmt_letVar_preserves_lookup _ _ "s" "authOff" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "authOff" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "authOff" _ _ hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "merkleNode" "authOff" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "mIdx" "authOff" _ (by decide) hexec

/-- The exact folded XMSS Merkle-climb state inside one accepting layer iteration. -/
def afterMerkle (ls : RuntimeState) : RuntimeState :=
  foldLoop "h" (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr")
    { beforeMerkle ls with
      bindings := bindValue (beforeMerkle ls).bindings "h" (wordNormalize 0) }
    0 (wordNormalize 11)

/-- The folded XMSS Merkle climb preserves the `"authOff"` binding initialized
before the loop. -/
theorem afterMerkle_authOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hAuthOffLt : sigOff + 692 < 2 ^ 256) :
    lookupValue (afterMerkle ls).bindings "authOff" = sigOff + 692 := by
  unfold afterMerkle
  rw [ClimbLoop.foldLoop_preserves_lookup "h" "authOff"
      (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr")
      (by decide) (fun s => merkleStep_preserves_authOff s)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "h" "authOff" _ (by decide)]
  exact beforeMerkle_authOff_eq_of_sigOff
    ls sigOff hSigOff hSigOffLt hCountOffLt hAuthOffLt

set_option maxHeartbeats 4000000 in
theorem suffix14_continues (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffix14 = .continue (stepLayer ls) := by
  unfold stepLayer suffix14 mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_merkleClimb "h" "merkleNode" "mIdx" "treeAdrs" "merklePtr" 11 _)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  rfl

/-- Once the Merkle loop state has been named, the final two layer assignments
continue to `stepLayer`. -/
theorem finalLayerTail_continues_from_afterMerkle (ls : RuntimeState) :
    execStmtList [] (afterMerkle ls)
        [ .assignVar "currentNode" (v "merkleNode")
        , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] =
      .continue (stepLayer ls) := by
  let suffixMerkleAndTail : List Stmt :=
    [ .forEach "h" (u 11) (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")
    , .assignVar "currentNode" (v "merkleNode")
    , .assignVar "sigOff" (addE (v "authOff") (u 176)) ]
  have h := suffix14_continues ls
  have hSplit : suffix14 = suffixBeforeMerkle ++ suffixMerkleAndTail := by
    rfl
  rw [hSplit] at h
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeMerkle_eq ls)] at h
  unfold suffixMerkleAndTail at h
  have hMerkle :
      execStmt [] (beforeMerkle ls)
          (.forEach "h" (u 11)
            (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")) =
        .continue (afterMerkle ls) := by
    simpa [afterMerkle, u] using
      (execStmt_forEach_merkleClimb
        "h" "merkleNode" "mIdx" "treeAdrs" "merklePtr" 11 (beforeMerkle ls))
  rw [execStmtList_cons_continue _ _ _ _ hMerkle] at h
  simpa [afterMerkle] using h

/-- The accepting layer suffix does not rebind `"idxTree"`. -/
theorem suffix14_preserves_idxTree (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "idxTree" =
      lookupValue (afterDigit ls).bindings "idxTree" := by
  refine execStmtList_preserves_lookup "idxTree" suffix14
    (afterDigit ls) (stepLayer ls) ?_ (suffix14_continues ls)
  intro s s'' stmt hmem hexec
  simp [suffix14, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "idxTree" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "idxTree" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "idxTree" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "idxTree" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody, mstoreE] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "idxTree" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "idxTree" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "idxTree" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "authOff" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "treeAdrs" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merkleNode" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "mIdx" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merklePtr" "idxTree" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "h" "idxTree" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [merkleClimbBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "sibling" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "parentIdx" "idxTree" _ (by decide) hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "s" "idxTree" _ (by decide) hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec'
        · exact execStmt_assignVar_preserves_lookup _ _ "merkleNode" "idxTree" _ (by decide) hexec'
        · exact execStmt_assignVar_preserves_lookup _ _ "mIdx" "idxTree" _ (by decide) hexec')
      hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "currentNode" "idxTree" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "sigOff" "idxTree" _ (by decide) hexec

/-- The accepting layer suffix does not rebind `"sigBase"`. -/
theorem suffix14_preserves_sigBase (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "sigBase" =
      lookupValue (afterDigit ls).bindings "sigBase" := by
  refine execStmtList_preserves_lookup "sigBase" suffix14
    (afterDigit ls) (stepLayer ls) ?_ (suffix14_continues ls)
  intro s s'' stmt hmem hexec
  simp [suffix14, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "sigBase" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "sigBase" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "sigBase" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "sigBase" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody, mstoreE] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "sigBase" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "sigBase" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "sigBase" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "authOff" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "treeAdrs" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merkleNode" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "mIdx" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merklePtr" "sigBase" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "h" "sigBase" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [merkleClimbBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "sibling" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "parentIdx" "sigBase" _ (by decide) hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "s" "sigBase" _ (by decide) hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec'
        · exact execStmt_assignVar_preserves_lookup _ _ "merkleNode" "sigBase" _ (by decide) hexec'
        · exact execStmt_assignVar_preserves_lookup _ _ "mIdx" "sigBase" _ (by decide) hexec')
      hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "currentNode" "sigBase" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "sigOff" "sigBase" _ (by decide) hexec

/-- One accepting layer iteration preserves selector/calldata from the incoming
guard state through the checksum prefix and layer suffix. -/
theorem stepLayer_preserves_selector_calldata (ls : RuntimeState) :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata ls (stepLayer ls) := by
  have hPrefix := afterDigit_preserves_selector_calldata ls
  have hSuffix :
      SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata
        (afterDigit ls) (stepLayer ls) :=
    SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
      suffix14 (afterDigit ls) (stepLayer ls)
      suffix14_preserves_selector_calldata (suffix14_continues ls)
  exact ⟨by rw [hSuffix.1, hPrefix.1], by rw [hSuffix.2, hPrefix.2]⟩

/-- One accepting layer iteration shifts the incoming `"idxTree"` by the C13
subtree height and carries that shifted value through the suffix. -/
theorem stepLayer_idxTree_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (stepLayer ls).bindings "idxTree" = idxTree / 2048 := by
  rw [suffix14_preserves_idxTree]
  rw [afterDigit_preserves_lookup_of_ne ls "idxTree" (by decide) (by decide)]
  exact beforeDigitLoop_idxTree_eq_of_idxTree ls idxTree hIdxTree hIdxTreeLt

/-- One accepting layer iteration preserves the `"sigBase"` binding. -/
theorem stepLayer_sigBase_eq (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "sigBase" =
      lookupValue ls.bindings "sigBase" := by
  rw [suffix14_preserves_sigBase]
  rw [afterDigit_preserves_lookup_of_ne ls "sigBase" (by decide) (by decide)]
  rw [beforeDigitLoop_preserves_sigBase]

/-- The final two layer assignments do not rebind `"merkleNode"`.  This is the
cheap tail brick used by structural layer-suffix proofs without replaying the
whole WOTS/XMSS prefix. -/
theorem finalLayerTail_preserves_merkleNode (st : RuntimeState) :
    lookupValue
        (match execStmtList [] st
            [ .assignVar "currentNode" (v "merkleNode")
            , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] with
          | .continue s' => s'
          | _ => st).bindings
        "merkleNode"
      = lookupValue st.bindings "merkleNode" := by
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_ne,
    ne_eq, String.reduceEq, not_false_eq_true]

/-- The final two layer assignments preserve scratch cell `0x00`. -/
theorem finalLayerTail_preserves_memory_zero (st : RuntimeState) :
    ((match execStmtList [] st
            [ .assignVar "currentNode" (v "merkleNode")
            , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] with
          | .continue s' => s'
          | _ => st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  rfl

/-- The final two layer assignments bind `"sigOff"` to `"authOff" + 176`. -/
theorem finalLayerTail_sigOff_eq_of_authOff
    (st : RuntimeState) (authOff : Nat)
    (hAuthOff : lookupValue st.bindings "authOff" = authOff)
    (hAuthOffLt : authOff < 2 ^ 256)
    (hSigOffLt : authOff + 176 < 2 ^ 256) :
    lookupValue
        (match execStmtList [] st
            [ .assignVar "currentNode" (v "merkleNode")
            , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] with
          | .continue s' => s'
          | _ => st).bindings
        "sigOff"
      = authOff + 176 := by
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (assignVar_continue _ "sigOff" _ (authOff + 176) (by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
          _ (v "authOff") (u 176) authOff 176
          (by
            change some (lookupValue (bindValue st.bindings "currentNode"
              (lookupValue st.bindings "merkleNode")) "authOff") = some authOff
            rw [MemoryKit.lookupValue_bindValue_ne _ "currentNode" "authOff" _ (by decide)]
            rw [hAuthOff])
          rfl hAuthOffLt (by decide : 176 < 2 ^ 256) hSigOffLt))]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_self]

/-- Running the final layer tail from the folded Merkle state advances
`"sigOff"` to the next layer's signature offset. -/
theorem afterMerkleTail_sigOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hAuthOffLt : sigOff + 692 < 2 ^ 256)
    (hNextSigOffLt : sigOff + 868 < 2 ^ 256) :
    lookupValue
        (match execStmtList [] (afterMerkle ls)
            [ .assignVar "currentNode" (v "merkleNode")
            , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] with
          | .continue s' => s'
          | _ => afterMerkle ls).bindings
        "sigOff" = sigOff + 868 := by
  have hAuth :
      lookupValue (afterMerkle ls).bindings "authOff" = sigOff + 692 :=
    afterMerkle_authOff_eq_of_sigOff
      ls sigOff hSigOff hSigOffLt hCountOffLt hAuthOffLt
  have hTail := finalLayerTail_sigOff_eq_of_authOff
    (afterMerkle ls) (sigOff + 692) hAuth hAuthOffLt
    (by
      have hSum : sigOff + 692 + 176 = sigOff + 868 := by omega
      simpa [hSum] using hNextSigOffLt)
  have hSum : sigOff + 692 + 176 = sigOff + 868 := by omega
  simpa [hSum] using hTail

/-- One accepting layer iteration advances `"sigOff"` past the WOTS count word
and XMSS auth path for that layer. -/
theorem stepLayer_sigOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hAuthOffLt : sigOff + 692 < 2 ^ 256)
    (hNextSigOffLt : sigOff + 868 < 2 ^ 256) :
    lookupValue (stepLayer ls).bindings "sigOff" = sigOff + 868 := by
  have hTail := afterMerkleTail_sigOff_eq_of_sigOff
    ls sigOff hSigOff hSigOffLt hCountOffLt hAuthOffLt hNextSigOffLt
  rw [finalLayerTail_continues_from_afterMerkle ls] at hTail
  exact hTail

set_option maxHeartbeats 4000000 in
/-- **`stepLayer_currentNode_eq_merkleNode`** — structural identification of the
*left* operand of the final `currentNode == root` compare.  The last two statements
of `suffix14` are `currentNode := merkleNode; sigOff := …`; neither reassigns
`merkleNode`, so in the post-iteration state the `"currentNode"` binding equals the
`"merkleNode"` binding — the output of the Merkle-climb `forEach "h"` loop.  This
pins the compare's left operand to the climb result *structurally*, without
evaluating any keccak (the climbed value is carried as an opaque bound term, peeled
by key only).  It is the first Phase-3b sub-brick on the open (left-operand) half:
the remaining obligation is to identify that climbed `merkleNode` value with the
abstract spec's `foldHypertree`/`xmssRootFromSig` root — the genuine keccak data
correspondence. -/
theorem stepLayer_currentNode_eq_merkleNode (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "currentNode"
      = lookupValue (stepLayer ls).bindings "merkleNode" := by
  unfold stepLayer suffix14 mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_merkleClimb "h" "merkleNode" "mIdx" "treeAdrs" "merklePtr" 11 _)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_ne, MemoryKit.lookupValue_bindValue_self,
    ne_eq, String.reduceEq, not_false_eq_true]

/-! ## 5. The guarded layer-body step lemma. -/

/-- The per-iteration guard: the checksum condition resolves to `0`
(`digitSum = 208`), i.e. the layer body does *not* revert. -/
def layerGuard (ls : RuntimeState) : Bool :=
  evalExpr [] (afterDigit ls) condE == some 0

/-- If the guard-free prefix's accumulated checksum binding is the C13 target
`208`, the executable layer guard passes.  This is a small public bridge from the
data-cell fact callers naturally prove (`"digitSum"` after `prefix11`) to the
guard predicate consumed by the guarded loop engine. -/
theorem layerGuard_of_afterDigit_digitSum_eq
    (ls : RuntimeState)
    (hDigit : lookupValue (afterDigit ls).bindings "digitSum" = 208) :
    layerGuard ls = true := by
  have hEq :
      evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208)) = some 1 := by
    unfold eqE v u
    show (do
      let lhs ← some (lookupValue (afterDigit ls).bindings "digitSum")
      let rhs ← some (wordNormalize 208)
      pure (boolWord (decide (lhs = rhs)))) = some 1
    rw [hDigit]
    rfl
  have hCond : evalExpr [] (afterDigit ls) condE = some 0 := by
    unfold condE notE
    show (do
      let value ← evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208))
      pure (boolWord (decide (value = 0)))) = some 0
    rw [hEq]
    rfl
  unfold layerGuard
  rw [hCond]
  rfl

/-- If the guard-free prefix's accumulated checksum binding is not the C13
target `208`, the executable layer guard fails. -/
theorem layerGuard_of_afterDigit_digitSum_ne
    (ls : RuntimeState)
    (hDigit : lookupValue (afterDigit ls).bindings "digitSum" ≠ 208) :
    layerGuard ls = false := by
  have hEq :
      evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208)) = some 0 := by
    unfold eqE v u
    have hNorm : wordNormalize 208 = 208 := by rfl
    change
      some (boolWord
        (decide (lookupValue (afterDigit ls).bindings "digitSum" = wordNormalize 208)))
        = some 0
    rw [hNorm]
    have hDec : decide (lookupValue (afterDigit ls).bindings "digitSum" = 208) = false := by
      exact decide_eq_false hDigit
    rw [hDec]
    rfl
  have hCond : evalExpr [] (afterDigit ls) condE = some 1 := by
    unfold condE notE
    show (do
      let value ← evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208))
      pure (boolWord (decide (value = 0)))) = some 1
    rw [hEq]
    rfl
  unfold layerGuard
  rw [hCond]
  rfl

/-- The checksum-guard `ite` (then = `revert0`, else = `[]`): continues with the
same state when its condition resolves to `0`, reverts otherwise. -/
private theorem ite_revert0_branch (st : RuntimeState) (cond : Expr) :
    execStmt [] st (.ite cond revert0 []) =
      match evalExpr [] st cond with
      | some r => if r != 0 then .revert else .continue st
      | none => .revert := by
  show (match evalExpr [] st cond with
        | some resolved =>
            if resolved != 0 then execStmtList [] st revert0 else execStmtList [] st []
        | none => .revert) = _
  cases evalExpr [] st cond with
  | none => rfl
  | some r => cases hr : r != 0 <;> simp only [hr, Bool.false_eq_true, if_true, if_false] <;> rfl

/-- **`execLayerBody`** — the guarded layer body: continues to `stepLayer ls`
when the checksum guard passes, reverts otherwise.  This is the `hstep`
hypothesis consumed by `ClimbLoopGuarded.execForEachLoop_of_guarded_step`. -/
theorem execLayerBody (ls : RuntimeState) :
    execStmtList [] ls layerBody
      = if layerGuard ls then .continue (stepLayer ls) else .revert := by
  unfold layerBody
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (afterDigit_eq ls)]
  rw [execStmtList_cons_eq, ite_revert0_branch]
  unfold layerGuard
  cases hc : evalExpr [] (afterDigit ls) condE with
  | none => rfl
  | some r =>
      by_cases hr : r = 0
      · subst hr
        simp only [bne_self_eq_false, beq_self_eq_true, reduceIte]
        exact suffix14_continues ls
      · have hb : (r != 0) = true := by simp [hr]
        have hb2 : (some r == some (0 : Nat)) = false := by simp [hr]
        simp only [hb, hb2]; rfl

/-! ## 6. The full guarded layer-loop fold. -/

/-- **`execLayerLoop`** — given that every threaded layer iteration's checksum
guard passes (`allGuardsPass`), the whole `forEach "layer" (u 2)` statement folds
to the pure `foldLoop` over `stepLayer`, exactly as the unguarded engine. -/
theorem execLayerLoop (state : RuntimeState)
    (hguards : ClimbLoopGuarded.allGuardsPass "layer" stepLayer layerGuard
        { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) } 0 (wordNormalize 2)) :
    execStmt [] state layerStmt
      = .continue
          (foldLoop "layer" stepLayer
            { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) }
            0 (wordNormalize 2)) :=
  ClimbLoopGuarded.execStmt_forEach_of_guarded_step "layer" (u 2) layerBody state (wordNormalize 2)
    stepLayer layerGuard rfl execLayerBody hguards

/-- The C13 two-layer climb loop reverts immediately when the first WOTS+C
checksum guard fails. -/
theorem execLayerLoop_reverts_on_first_guard
    (state : RuntimeState)
    (hguard :
      layerGuard
        (ClimbLoopGuarded.loopState "layer"
          { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) } 0)
        = false) :
    execStmt [] state layerStmt = .revert := by
  exact
    ClimbLoopGuarded.execStmt_forEach_revert_on_first_guard
      "layer" (u 2) layerBody state (wordNormalize 2)
      stepLayer layerGuard rfl
      1
      (SegmentS2.wordNormalize_of_lt (by decide : 2 < 2 ^ 256))
      execLayerBody hguard

/-- The C13 two-layer climb loop reverts on the second iteration when the first
WOTS+C checksum guard passes but the second one fails after the first
`stepLayer`. -/
theorem execLayerLoop_reverts_on_second_guard
    (state : RuntimeState)
    (hguard0 :
      layerGuard
        (ClimbLoopGuarded.loopState "layer"
          { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) } 0)
        = true)
    (hguard1 :
      layerGuard
        (ClimbLoopGuarded.loopState "layer"
          (stepLayer
            (ClimbLoopGuarded.loopState "layer"
              { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) } 0))
          1)
        = false) :
    execStmt [] state layerStmt = .revert := by
  exact
    ClimbLoopGuarded.execStmt_forEach_revert_on_second_guard
      "layer" (u 2) layerBody state (wordNormalize 2)
      stepLayer layerGuard rfl
      0
      (SegmentS2.wordNormalize_of_lt (by decide : 2 < 2 ^ 256))
      execLayerBody hguard0 hguard1

/-! ## 7. Axiom audit. -/

#print axioms layerStmt_eq_slice
#print axioms digitSumStep_digitSum_expr
#print axioms digitSumStep_preserves_lookup_of_ne
#print axioms nat_land_low3
#print axioms nat_land_low11
#print axioms digitSumStep_digitSum_eq_add_digit
#print axioms afterDigitFold_preserves_lookup_of_ne
#print axioms beforeDigitLoop_eq
#print axioms beforeDigitLoop_preserves_sigBase
#print axioms beforeDigitLoop_countOff_eq_of_sigOff
#print axioms beforeDigest_eq
#print axioms beforeDigest_preserves_memory_zero
#print axioms beforeDigitLoop_preserves_memory_zero
#print axioms afterDigitFold_preserves_memory_zero
#print axioms afterDigit_preserves_memory_zero
#print axioms stepWots_preserves_lookup_of_ne
#print axioms stepWots_preserves_memory_zero
#print axioms wotsChainFold_preserves_memory_zero
#print axioms wotsChainFold_preserves_i_lookup
#print axioms wotsOuterPrefix_preserves_memory_zero
#print axioms wotsOuterPrefix_preserves_i_lookup
#print axioms wotsOuterBody_preserves_memory_zero_of_i
#print axioms wotsOuterStep_preserves_memory_zero_of_i
#print axioms wotsOuterBody_preserves_i_lookup
#print axioms wotsOuterStep_preserves_i_lookup
#print axioms wotsOuterFold_preserves_memory_zero
#print axioms copyStep_preserves_memory_zero_of_i
#print axioms copyFold_preserves_memory_zero
#print axioms beforeDigest_idxLeaf_eq_of_idxTree
#print axioms beforeDigest_idxTree_eq_of_idxTree
#print axioms beforeDigitLoop_idxTree_eq_of_idxTree
#print axioms beforeDigest_wotsAdrs_eq_of_layer_idxTree
#print axioms beforeDigest_count_eq_of_sigBase_sigOff_calldata
#print axioms beforeDigest_memory_0x20_eq_of_wotsAdrs
#print axioms beforeDigest_memory_0x40_eq_currentNode
#print axioms beforeDigest_memory_0x40_eq_wordOfHash16
#print axioms beforeDigest_memory_0x60_eq_of_count
#print axioms beforeDigitLoop_d_eq_keccakWords
#print axioms beforeDigitLoop_d_eq_wotsDigest_of_scratch
#print axioms afterDigit_preserves_selector_calldata
#print axioms digitSumBody_preserves_selector_calldata
#print axioms wotsChainBody_preserves_selector_calldata
#print axioms copyBody_preserves_selector_calldata
#print axioms merkleClimbBody_preserves_selector_calldata
#print axioms wotsOuterBody_preserves_selector_calldata
#print axioms suffix14_preserves_selector_calldata
#print axioms suffix14_preserves_idxTree
#print axioms suffix14_preserves_sigBase
#print axioms prefix11_eq_afterDigitFold
#print axioms afterDigit_eq_afterDigitFold
#print axioms afterDigit_digitSum_eq_afterDigitFold
#print axioms afterDigit_preserves_lookup_of_ne
#print axioms afterDigitFold_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
#print axioms afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
#print axioms layerGuard_of_afterDigit_digitSum_eq
#print axioms layerGuard_of_afterDigit_digitSum_ne
#print axioms beforeAuthOff_eq
#print axioms beforeAuthOff_preserves_memory_zero_of_loop_frames
#print axioms suffixBeforeAuthOff_preserves_countOff
#print axioms beforeAuthOff_countOff_eq_of_sigOff
#print axioms beforeMerkle_eq
#print axioms suffixBeforeMerkle_preserves_countOff
#print axioms beforeMerkle_countOff_eq_of_sigOff
#print axioms beforeMerkle_authOff_eq_of_sigOff
#print axioms merkleStep_preserves_authOff
#print axioms afterMerkle_authOff_eq_of_sigOff
#print axioms finalLayerTail_continues_from_afterMerkle
#print axioms stepLayer_sigOff_eq_of_sigOff
#print axioms stepLayer_preserves_selector_calldata
#print axioms stepLayer_idxTree_eq_of_idxTree
#print axioms stepLayer_sigBase_eq
#print axioms finalLayerTail_preserves_merkleNode
#print axioms finalLayerTail_preserves_memory_zero
#print axioms finalLayerTail_sigOff_eq_of_authOff
#print axioms afterMerkleTail_sigOff_eq_of_sigOff
#print axioms execLayerBody
#print axioms execLayerLoop
#print axioms execLayerLoop_reverts_on_first_guard
#print axioms execLayerLoop_reverts_on_second_guard
#print axioms stepLayer_currentNode_eq_merkleNode

end SphincsMinusVerifiers.SegmentLayer3
