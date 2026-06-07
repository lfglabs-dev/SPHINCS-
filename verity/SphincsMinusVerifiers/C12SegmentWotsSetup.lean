import SphincsMinusVerifiers.C12SegmentForsCompress
import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ProofCore
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.ClimbMemFrameMerkle

namespace SphincsMinusVerifiers.C12SegmentWotsSetup

open Compiler.CompilationModel (Stmt Expr)
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbKit (N_MASK execStmtList_cons_continue)
open SphincsMinusVerifiers.ClimbLoop (execStmt_forEach_of_step)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue execStmtList_append_continue)

def u (n : Nat) : Expr := .literal n
def v (name : String) : Expr := .localVar name
def addE (a b : Expr) : Expr := .add a b
def subE (a b : Expr) : Expr := .sub a b
def mulE (a b : Expr) : Expr := .mul a b
def andE (a b : Expr) : Expr := .bitAnd a b
def orE (a b : Expr) : Expr := .bitOr a b
def xorE (a b : Expr) : Expr := .bitXor a b
def shlE (a b : Expr) : Expr := .shl a b
def shrE (a b : Expr) : Expr := .shr a b
def cdload (off : Expr) : Expr := .calldataload off
def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
def mloadE (off : Expr) : Expr := .mload off
def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
def mstoreE (off val : Expr) : Stmt := .mstore off val

theorem assignVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.assignVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

def c12WotsChainBody : List Stmt := [
  mstore 0x20 (orE (v "chainBase") (shlE (u 32) (addE (v "digit") (v "s")))),
  mstore 0x40 (v "val"),
  .assignVar "val" (andE (keccak 0x00 0x60) (u N_MASK))
]

def c12WotsChainStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12WotsChainBody with
  | .continue s' => s'
  | _ => st

theorem execC12WotsChainBody (st : RuntimeState) :
    execStmtList [] st c12WotsChainBody = .continue (c12WotsChainStep st) := by
  unfold c12WotsChainStep c12WotsChainBody mstore
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "val" _ _ rfl)]
  rfl

/-- One C12 WOTS hash-chain body preserves the public-seed scratch cell. -/
theorem c12WotsChainStep_preserves_memory_zero (st : RuntimeState) :
    ((c12WotsChainStep st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 c12WotsChainBody st (c12WotsChainStep st) ?_
    (execC12WotsChainBody st)
  intro s s'' stmt hmem hexec
  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ 0x00 _ _ ?_ hexec
    intro ro rv hoff hval
    change evalExpr [] s (.literal 0x20) = some ro at hoff
    rw [show evalExpr [] s (.literal 0x20) = some 0x20 from rfl] at hoff
    injection hoff with hro
    subst ro
    decide
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ 0x00 _ _ ?_ hexec
    intro ro rv hoff hval
    change evalExpr [] s (.literal 0x40) = some ro at hoff
    rw [show evalExpr [] s (.literal 0x40) = some 0x40 from rfl] at hoff
    injection hoff with hro
    subst ro
    decide
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
      _ _ 0x00 "val" _ hexec

theorem c12WotsChainBody_preserves_memory_zero :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12WotsChainBody → execStmt [] s stmt = .continue s'' →
      (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  intro s s'' stmt hmem hexec
  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ 0x00 _ _ ?_ hexec
    intro ro rv hoff hval
    change evalExpr [] s (.literal 0x20) = some ro at hoff
    rw [show evalExpr [] s (.literal 0x20) = some 0x20 from rfl] at hoff
    cases hoff
    decide
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ 0x00 _ _ ?_ hexec
    intro ro rv hoff hval
    change evalExpr [] s (.literal 0x40) = some ro at hoff
    rw [show evalExpr [] s (.literal 0x40) = some 0x40 from rfl] at hoff
    cases hoff
    decide
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
      _ _ 0x00 "val" _ hexec

/-- One C12 WOTS hash-chain body statement preserves every memory cell except
the two scratch words it may write. -/
theorem c12WotsChainBody_preserves_memory_addr_of_ne
    (addr : Nat) (h20 : addr ≠ 0x20) (h40 : addr ≠ 0x40) :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12WotsChainBody → execStmt [] s stmt = .continue s'' →
      (s''.world.memory addr).val = (s.world.memory addr).val := by
  intro s s'' stmt hmem hexec
  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ addr _ _ ?_ hexec
    intro ro rv hoff hval
    change evalExpr [] s (.literal 0x20) = some ro at hoff
    rw [show evalExpr [] s (.literal 0x20) = some 0x20 from rfl] at hoff
    cases hoff
    exact h20
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ addr _ _ ?_ hexec
    intro ro rv hoff hval
    change evalExpr [] s (.literal 0x40) = some ro at hoff
    rw [show evalExpr [] s (.literal 0x40) = some 0x40 from rfl] at hoff
    cases hoff
    exact h40
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
      _ _ addr "val" _ hexec

/-- One C12 WOTS-chain inner step computes one `chainHashC12`-style Keccak.
With memory[0x00] holding `seed`, and the bindings carrying `chainBase`,
`digit`, `s` (inner step index), and `val` (the previous chain word), one
`c12WotsChainStep` updates `"val"` to the masked Keccak preimage
`[seed, chainBase ||| ((digit + s) <<< 32), prevVal]`. -/
theorem c12WotsChainStep_val_eq
    (s : RuntimeState) (seed chainBase digit sIdx prevVal : Nat)
    (hSeed : (s.world.memory 0x00).val = seed)
    (hCB : lookupValue s.bindings "chainBase" = chainBase)
    (hDigit : lookupValue s.bindings "digit" = digit)
    (hS : lookupValue s.bindings "s" = sIdx)
    (hVal : lookupValue s.bindings "val" = prevVal)
    (hCBlt : chainBase < 2 ^ 256)
    (hDigitLt : digit < 2 ^ 256) (hSIdxLt : sIdx < 2 ^ 256)
    (hSum : digit + sIdx < 2 ^ 256)
    (hShift : (digit + sIdx) <<< 32 < 2 ^ 256)
    (hPrevLt : prevVal < 2 ^ 256) :
    lookupValue (c12WotsChainStep s).bindings "val" =
      SphincsMinusVerifierSpec.C13Concrete.maskN
        (SphincsMinusVerifierSpec.C13Concrete.keccakWords
          [seed, chainBase ||| ((digit + sIdx) <<< 32), prevVal]) := by
  have h32 : evalExpr [] s (u 32) = some 32 := by
    show some (wordNormalize 32) = some 32
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hCBeval : evalExpr [] s (v "chainBase") = some chainBase := by
    show some (lookupValue s.bindings "chainBase") = some chainBase
    rw [hCB]
  have hDigitEval : evalExpr [] s (v "digit") = some digit := by
    show some (lookupValue s.bindings "digit") = some digit
    rw [hDigit]
  have hSEval : evalExpr [] s (v "s") = some sIdx := by
    show some (lookupValue s.bindings "s") = some sIdx
    rw [hS]
  have hSumEval : evalExpr [] s (addE (v "digit") (v "s")) = some (digit + sIdx) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded s
      (v "digit") (v "s") digit sIdx hDigitEval hSEval hDigitLt hSIdxLt hSum
  have hShlEval : evalExpr [] s (shlE (u 32) (addE (v "digit") (v "s"))) =
      some ((digit + sIdx) <<< 32) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded s
      (u 32) (addE (v "digit") (v "s")) 32 (digit + sIdx) h32 hSumEval
      (by decide) hSum hShift
  have hAdrsEval : evalExpr [] s
      (orE (v "chainBase") (shlE (u 32) (addE (v "digit") (v "s")))) =
        some (chainBase ||| ((digit + sIdx) <<< 32)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded s
      (v "chainBase") (shlE (u 32) (addE (v "digit") (v "s")))
      chainBase ((digit + sIdx) <<< 32) hCBeval hShlEval hCBlt hShift
  set adrsWord : Nat := chainBase ||| ((digit + sIdx) <<< 32) with hAdrsDef
  have hAdrsLt : adrsWord < 2 ^ 256 := by
    show Nat.bitwise or chainBase ((digit + sIdx) <<< 32) < 2 ^ 256
    exact Nat.bitwise_lt_two_pow hCBlt hShift
  have h0x20Lit : evalExpr [] s (u 0x20) = some 0x20 := by
    show some (wordNormalize 0x20) = some 0x20
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  let s1 : RuntimeState :=
    { s with world := { s.world with
        memory := SphincsMinusVerifiers.MemoryKit.memUpdate s.world.memory 0x20 adrsWord } }
  have hStep1 : execStmt [] s
      (mstore 0x20 (orE (v "chainBase") (shlE (u 32) (addE (v "digit") (v "s"))))) =
        .continue s1 := by
    unfold mstore
    exact SphincsMinusVerifiers.MemoryKit.execStmt_mstore_continue s (u 0x20)
      (orE (v "chainBase") (shlE (u 32) (addE (v "digit") (v "s"))))
      0x20 adrsWord h0x20Lit hAdrsEval
  have hValEval_s1 : evalExpr [] s1 (v "val") = some prevVal := by
    show some (lookupValue s1.bindings "val") = some prevVal
    change some (lookupValue s.bindings "val") = some prevVal
    rw [hVal]
  have h0x40Lit : evalExpr [] s1 (u 0x40) = some 0x40 := by
    show some (wordNormalize 0x40) = some 0x40
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  let s2 : RuntimeState :=
    { s1 with world := { s1.world with
        memory := SphincsMinusVerifiers.MemoryKit.memUpdate s1.world.memory 0x40 prevVal } }
  have hStep2 : execStmt [] s1 (mstore 0x40 (v "val")) = .continue s2 := by
    unfold mstore
    exact SphincsMinusVerifiers.MemoryKit.execStmt_mstore_continue s1 (u 0x40) (v "val")
      0x40 prevVal h0x40Lit hValEval_s1
  have hMem0 : (s2.world.memory 0x00).val = seed := by
    show (SphincsMinusVerifiers.MemoryKit.memUpdate
        (SphincsMinusVerifiers.MemoryKit.memUpdate s.world.memory 0x20 adrsWord)
        0x40 prevVal 0x00).val = seed
    rw [SphincsMinusVerifiers.MemoryKit.memUpdate_diff _ 0x40 0x00 _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.memUpdate_diff _ 0x20 0x00 _ (by decide)]
    exact hSeed
  have hMem20 : (s2.world.memory 0x20).val = adrsWord := by
    show (SphincsMinusVerifiers.MemoryKit.memUpdate
        (SphincsMinusVerifiers.MemoryKit.memUpdate s.world.memory 0x20 adrsWord)
        0x40 prevVal 0x20).val = adrsWord
    rw [SphincsMinusVerifiers.MemoryKit.memUpdate_diff _ 0x40 0x20 _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.memUpdate_val_same]
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hAdrsLt]
  have hMem40 : (s2.world.memory 0x40).val = prevVal := by
    show (SphincsMinusVerifiers.MemoryKit.memUpdate
        (SphincsMinusVerifiers.MemoryKit.memUpdate s.world.memory 0x20 adrsWord)
        0x40 prevVal 0x40).val = prevVal
    rw [SphincsMinusVerifiers.MemoryKit.memUpdate_val_same]
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hPrevLt]
  have hOff : wordNormalize (0 : Nat) = 0 := by
    rw [wordNormalize_eq_mod]; exact Nat.zero_mod _
  have hWsLen : (32 : Nat) * [seed, adrsWord, prevVal].length < 2 ^ 256 := by
    show (32 : Nat) * 3 < 2 ^ 256
    decide
  have hMem : ∀ i, (h : i < [seed, adrsWord, prevVal].length) →
      (s2.world.memory (0 + 32 * i)).val = [seed, adrsWord, prevVal][i] := by
    intro i hi
    match i with
    | 0 => simpa using hMem0
    | 1 => simpa using hMem20
    | 2 => simpa using hMem40
  have hKecEval :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_maskedKeccak_eq_maskN
      s2 0 [seed, adrsWord, prevVal] hOff hWsLen hMem
  have hSz3 : (32 : Nat) * [seed, adrsWord, prevVal].length = 0x60 := by
    show (32 : Nat) * 3 = 0x60
    decide
  rw [hSz3] at hKecEval
  have hMaskEq : (SphincsMinusVerifierSpec.C13Concrete.nMask : Nat) = N_MASK := rfl
  rw [hMaskEq] at hKecEval
  change evalExpr [] s2 (andE (keccak 0x00 0x60) (u N_MASK)) =
      some (SphincsMinusVerifierSpec.C13Concrete.maskN
        (SphincsMinusVerifierSpec.C13Concrete.keccakWords
          [seed, adrsWord, prevVal])) at hKecEval
  have hStep3 : execStmt [] s2
      (.assignVar "val" (andE (keccak 0x00 0x60) (u N_MASK))) =
        .continue { s2 with
          bindings := bindValue s2.bindings "val"
            (SphincsMinusVerifierSpec.C13Concrete.maskN
              (SphincsMinusVerifierSpec.C13Concrete.keccakWords
                [seed, adrsWord, prevVal])) } :=
    assignVar_continue s2 "val" _ _ hKecEval
  have hExec : execStmtList [] s c12WotsChainBody =
      .continue { s2 with
        bindings := bindValue s2.bindings "val"
          (SphincsMinusVerifierSpec.C13Concrete.maskN
            (SphincsMinusVerifierSpec.C13Concrete.keccakWords
              [seed, adrsWord, prevVal])) } := by
    unfold c12WotsChainBody
    rw [execStmtList_cons_continue _ _ _ _ hStep1]
    rw [execStmtList_cons_continue _ _ _ _ hStep2]
    rw [execStmtList_cons_continue _ _ _ _ hStep3]
    rfl
  unfold c12WotsChainStep
  rw [hExec]
  exact SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self _ _ _

/-- `c12WotsChainStep` only updates the `"val"` binding; every other key is
preserved.  Frame fact used in the chain inner-loop induction. -/
theorem c12WotsChainStep_preserves_lookup_of_ne_val
    (key : String) (hne : "val" ≠ key) (st : RuntimeState) :
    lookupValue (c12WotsChainStep st).bindings key =
      lookupValue st.bindings key :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    key c12WotsChainBody st (c12WotsChainStep st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ key _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ key _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
          _ _ "val" key _ hne hexec)
    (execC12WotsChainBody st)

/-- The C12 WOTS-chain inner loop semantics.  Running `foldLoop "s" c12WotsChainStep`
over the inner-step body computes one full chain-hash sequence: starting from
`val = val0` and stepping `remaining` times from inner-step `index`, the final
`"val"` binding equals `chainHashC12 seed chainBase digit remaining index val0`.

The bounds `chainBase < 2^256`, `digit ≤ 7`, `index + remaining ≤ 7` cover every
WOTS use site (digits are 3-bit, chain depth is `7 - digit ≤ 7`); the per-step
hypotheses on `state` are the WOTS-body invariant. -/
theorem c12WotsChain_foldLoop_val_eq
    (seed chainBase digit : Nat)
    (hCBlt : chainBase < 2 ^ 256) (hDigitLe : digit ≤ 7) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (state.world.memory 0x00).val = seed →
      lookupValue state.bindings "chainBase" = chainBase →
      lookupValue state.bindings "digit" = digit →
      lookupValue state.bindings "val" < 2 ^ 256 →
      index + remaining ≤ 7 →
      lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "s" c12WotsChainStep
            state index remaining).bindings "val" =
        SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
          remaining index (lookupValue state.bindings "val") := by
  intro state index remaining
  induction remaining generalizing state index with
  | zero =>
      intro _ _ _ _ _
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
      rfl
  | succ r ih =>
      intro hSeed hCB hDigit hValLt hSum
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      have hIdxLe : index ≤ 7 := by omega
      have hIdxLt256 : index < 2 ^ 256 := by
        have : index ≤ 7 := hIdxLe
        have h7 : (7 : Nat) < 2 ^ 256 := by decide
        omega
      have hWnIdx : wordNormalize index = index := by
        rw [wordNormalize_eq_mod,
          show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt hIdxLt256]
      have hDigitLt256 : digit < 2 ^ 256 := by
        have h7 : (7 : Nat) < 2 ^ 256 := by decide
        omega
      have hSumLe : digit + index ≤ 14 := by omega
      have hSumLt256 : digit + index < 2 ^ 256 := by
        have h14 : (14 : Nat) < 2 ^ 256 := by decide
        omega
      have hShiftLt : (digit + index) <<< 32 < 2 ^ 256 := by
        rw [Nat.shiftLeft_eq]
        have hmul : (digit + index) * 2 ^ 32 ≤ 14 * 2 ^ 32 :=
          Nat.mul_le_mul_right _ hSumLe
        have h14 : (14 : Nat) * 2 ^ 32 < 2 ^ 256 := by decide
        omega
      -- The bound state after binding "s" = wordNormalize index
      let state1 : RuntimeState :=
        { state with bindings := bindValue state.bindings "s" (wordNormalize index) }
      have hCB1 : lookupValue state1.bindings "chainBase" = chainBase := by
        show lookupValue (bindValue state.bindings "s" (wordNormalize index)) "chainBase" =
              chainBase
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
              state.bindings "s" "chainBase" _ (by decide)]
        exact hCB
      have hDigit1 : lookupValue state1.bindings "digit" = digit := by
        show lookupValue (bindValue state.bindings "s" (wordNormalize index)) "digit" = digit
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
              state.bindings "s" "digit" _ (by decide)]
        exact hDigit
      have hVal1 : lookupValue state1.bindings "val" = lookupValue state.bindings "val" := by
        show lookupValue (bindValue state.bindings "s" (wordNormalize index)) "val" = _
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
              state.bindings "s" "val" _ (by decide)]
      have hS1 : lookupValue state1.bindings "s" = index := by
        show lookupValue (bindValue state.bindings "s" (wordNormalize index)) "s" = index
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
          hWnIdx]
      have hMem1 : (state1.world.memory 0x00).val = seed := hSeed
      -- Apply M3a at state1
      have hVal2 : lookupValue (c12WotsChainStep state1).bindings "val" =
          SphincsMinusVerifierSpec.C13Concrete.maskN
            (SphincsMinusVerifierSpec.C13Concrete.keccakWords
              [seed, chainBase ||| ((digit + index) <<< 32),
                lookupValue state.bindings "val"]) := by
        have hPrevLt : lookupValue state.bindings "val" < 2 ^ 256 := hValLt
        have h := c12WotsChainStep_val_eq state1 seed chainBase digit index
          (lookupValue state.bindings "val") hMem1 hCB1 hDigit1 hS1 hVal1
          hCBlt hDigitLt256 hIdxLt256 hSumLt256 hShiftLt hPrevLt
        exact h
      -- Memory and bindings on state2 := c12WotsChainStep state1 for IH
      have hMem2 : ((c12WotsChainStep state1).world.memory 0x00).val = seed := by
        rw [c12WotsChainStep_preserves_memory_zero state1]
        exact hMem1
      have hCB2 : lookupValue (c12WotsChainStep state1).bindings "chainBase" =
          chainBase := by
        rw [c12WotsChainStep_preserves_lookup_of_ne_val "chainBase"
          (by decide) state1]
        exact hCB1
      have hDigit2 : lookupValue (c12WotsChainStep state1).bindings "digit" = digit := by
        rw [c12WotsChainStep_preserves_lookup_of_ne_val "digit"
          (by decide) state1]
        exact hDigit1
      have hVal2Lt : lookupValue (c12WotsChainStep state1).bindings "val" < 2 ^ 256 := by
        rw [hVal2]
        show Nat.bitwise and _ SphincsMinusVerifierSpec.C13Concrete.nMask < 2 ^ 256
        apply Nat.bitwise_lt_two_pow
        · have := SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
            [seed, chainBase ||| ((digit + index) <<< 32),
              lookupValue state.bindings "val"]
          rwa [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl] at this
        · exact SphincsMinusVerifiers.ClimbKeccakStep.nMask_lt
      have hSum2 : (index + 1) + r ≤ 7 := by omega
      -- Apply IH
      have hIH := ih (c12WotsChainStep state1) (index + 1)
        hMem2 hCB2 hDigit2 hVal2Lt hSum2
      -- Replace state1 to match `foldLoop_succ` shape
      show lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "s" c12WotsChainStep
          (c12WotsChainStep state1) (index + 1) r).bindings "val" =
        SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
          (r + 1) index (lookupValue state.bindings "val")
      rw [hIH, hVal2]
      rfl

def c12WotsMessageBody : List Stmt := [
  .letVar "digit" (andE (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) (u 7)),
  .assignVar "csum" (addE (v "csum") (subE (u 7) (v "digit"))),
  .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)),
  .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i"))),
  .letVar "steps" (subE (u 7) (v "digit")),
  .forEach "s" (v "steps") c12WotsChainBody,
  mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
]

def c12WotsMessagePrefix : List Stmt := [
  .letVar "digit" (andE (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) (u 7)),
  .assignVar "csum" (addE (v "csum") (subE (u 7) (v "digit"))),
  .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)),
  .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i"))),
  .letVar "steps" (subE (u 7) (v "digit")),
  .forEach "s" (v "steps") c12WotsChainBody
]

theorem c12WotsMessageBody_eq_prefix_tail :
    c12WotsMessageBody =
      c12WotsMessagePrefix ++
        [mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")] := rfl

def c12WotsMessageStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12WotsMessageBody with
  | .continue s' => s'
  | _ => st

theorem execC12WotsMessageBody (st : RuntimeState) :
    execStmtList [] st c12WotsMessageBody = .continue (c12WotsMessageStep st) := by
  unfold c12WotsMessageStep c12WotsMessageBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "digit" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "val" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "chainBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "steps" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "s" (v "steps") c12WotsChainBody _ _
      c12WotsChainStep rfl execC12WotsChainBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- One C12 WOTS message-loop iteration preserves every binding outside its
local temporaries and checksum accumulator. -/
theorem c12WotsMessageStep_preserves_lookup_of_fresh
    (key : String)
    (hDigit : "digit" ≠ key)
    (hCsum : "csum" ≠ key)
    (hVal : "val" ≠ key)
    (hChainBase : "chainBase" ≠ key)
    (hSteps : "steps" ≠ key)
    (hS : "s" ≠ key)
    (st : RuntimeState) :
    lookupValue (c12WotsMessageStep st).bindings key =
      lookupValue st.bindings key := by
  exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    key c12WotsMessageBody st (c12WotsMessageStep st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12WotsMessageBody, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "digit" key _ hDigit hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
          _ _ "csum" key _ hCsum hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "val" key _ hVal hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "chainBase" key _ hChainBase hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "steps" key _ hSteps hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "s" key _ _ _ _ hS
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ key _ _ hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ key _ _ hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                _ _ "val" key _ hVal hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ key _ _ hexec)
    (execC12WotsMessageBody st)

theorem c12WotsMessagePrefix_preserves_memory_zero
    (st s' : RuntimeState)
    (hExec : execStmtList [] st c12WotsMessagePrefix = .continue s') :
    (s'.world.memory 0x00).val = (st.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 c12WotsMessagePrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp only [c12WotsMessagePrefix, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "digit" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
      _ _ 0x00 "csum" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "val" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "chainBase" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "steps" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val
      "s" 0x00 (v "steps") c12WotsChainBody _ _ c12WotsChainBody_preserves_memory_zero
      hexec

theorem c12WotsMessagePrefix_preserves_i
    (st s' : RuntimeState)
    (hExec : execStmtList [] st c12WotsMessagePrefix = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i" c12WotsMessagePrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp only [c12WotsMessagePrefix, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "digit" "i" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "csum" "i" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "val" "i" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "chainBase" "i" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "steps" "i" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "s" "i" _ _ _ _ (by decide)
      (by
        intro s s'' stmt hmem hexec
        simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            _ _ "i" _ _ hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            _ _ "i" _ _ hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            _ _ "val" "i" _ (by decide) hexec)
      hexec

theorem c12WotsMessagePrefix_preserves_memory_addr_of_ne
    (addr : Nat) (h20 : addr ≠ 0x20) (h40 : addr ≠ 0x40)
    (st s' : RuntimeState)
    (hExec : execStmtList [] st c12WotsMessagePrefix = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    addr c12WotsMessagePrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp only [c12WotsMessagePrefix, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ addr "digit" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
      _ _ addr "csum" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ addr "val" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ addr "chainBase" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ addr "steps" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val
      "s" addr (v "steps") c12WotsChainBody _ _
      (c12WotsChainBody_preserves_memory_addr_of_ne addr h20 h40) hexec

def c12WotsChecksumBody : List Stmt := [
  .letVar "digit" (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)),
  .letVar "i" (addE (u 42) (v "j")),
  .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)),
  .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i"))),
  .letVar "steps" (subE (u 7) (v "digit")),
  .forEach "s" (v "steps") c12WotsChainBody,
  mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
]

def c12WotsChecksumPrefix : List Stmt := [
  .letVar "digit" (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)),
  .letVar "i" (addE (u 42) (v "j")),
  .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)),
  .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i"))),
  .letVar "steps" (subE (u 7) (v "digit")),
  .forEach "s" (v "steps") c12WotsChainBody
]

theorem c12WotsChecksumBody_eq_prefix_tail :
    c12WotsChecksumBody =
      c12WotsChecksumPrefix ++
        [mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")] := rfl

def c12WotsChecksumStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12WotsChecksumBody with
  | .continue s' => s'
  | _ => st

theorem execC12WotsChecksumBody (st : RuntimeState) :
    execStmtList [] st c12WotsChecksumBody = .continue (c12WotsChecksumStep st) := by
  unfold c12WotsChecksumStep c12WotsChecksumBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "digit" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "i" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "val" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "chainBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "steps" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "s" (v "steps") c12WotsChainBody _ _
      c12WotsChainStep rfl execC12WotsChainBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- One C12 WOTS checksum-loop iteration preserves every binding outside its
local temporaries. -/
theorem c12WotsChecksumStep_preserves_lookup_of_fresh
    (key : String)
    (hDigit : "digit" ≠ key)
    (hI : "i" ≠ key)
    (hVal : "val" ≠ key)
    (hChainBase : "chainBase" ≠ key)
    (hSteps : "steps" ≠ key)
    (hS : "s" ≠ key)
    (st : RuntimeState) :
    lookupValue (c12WotsChecksumStep st).bindings key =
      lookupValue st.bindings key := by
  exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    key c12WotsChecksumBody st (c12WotsChecksumStep st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12WotsChecksumBody, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "digit" key _ hDigit hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "i" key _ hI hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "val" key _ hVal hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "chainBase" key _ hChainBase hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "steps" key _ hSteps hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "s" key _ _ _ _ hS
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ key _ _ hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ key _ _ hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                _ _ "val" key _ hVal hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ key _ _ hexec)
    (execC12WotsChecksumBody st)

theorem c12WotsChecksumPrefix_preserves_memory_zero
    (st s' : RuntimeState)
    (hExec : execStmtList [] st c12WotsChecksumPrefix = .continue s') :
    (s'.world.memory 0x00).val = (st.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 c12WotsChecksumPrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp only [c12WotsChecksumPrefix, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "digit" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "i" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "val" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "chainBase" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "steps" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val
      "s" 0x00 (v "steps") c12WotsChainBody _ _ c12WotsChainBody_preserves_memory_zero
      hexec

theorem c12WotsChecksumPrefix_preserves_memory_addr_of_ne
    (addr : Nat) (h20 : addr ≠ 0x20) (h40 : addr ≠ 0x40)
    (st s' : RuntimeState)
    (hExec : execStmtList [] st c12WotsChecksumPrefix = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    addr c12WotsChecksumPrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp only [c12WotsChecksumPrefix, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ addr "digit" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ addr "i" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ addr "val" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ addr "chainBase" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ addr "steps" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val
      "s" addr (v "steps") c12WotsChainBody _ _
      (c12WotsChainBody_preserves_memory_addr_of_ne addr h20 h40) hexec

theorem c12WotsChecksumTail_preserves_i
    (st s' : RuntimeState)
    (hExec : execStmtList [] st
      [ .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
      , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
      , .letVar "steps" (subE (u 7) (v "digit"))
      , .forEach "s" (v "steps") c12WotsChainBody ] = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i"
    [ .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
    , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
    , .letVar "steps" (subE (u 7) (v "digit"))
    , .forEach "s" (v "steps") c12WotsChainBody ] st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "val" "i" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "chainBase" "i" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "steps" "i" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "s" "i" _ _ _ _ (by decide)
      (by
        intro s s'' stmt hmem hexec
        simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            _ _ "i" _ _ hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            _ _ "i" _ _ hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            _ _ "val" "i" _ (by decide) hexec)
      hexec

def c12WotsPkCopyBody : List Stmt := [
  mstoreE (addE (u 0x40) (shlE (u 5) (v "i")))
    (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
]

def c12WotsPkCopyStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12WotsPkCopyBody with
  | .continue s' => s'
  | _ => st

theorem execC12WotsPkCopyBody (st : RuntimeState) :
    execStmtList [] st c12WotsPkCopyBody = .continue (c12WotsPkCopyStep st) := by
  unfold c12WotsPkCopyStep c12WotsPkCopyBody mstoreE mloadE
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

theorem c12_wots_idxNorm67 (idx : Nat) (hidx : idx < 67) :
    wordNormalize idx = idx := by
  rw [wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt (lt_trans hidx (by decide))

theorem c12_wots_idxShl5_lt67 (idx : Nat) (hidx : idx < 67) :
    idx <<< 5 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : idx * 2 ^ 5 ≤ 66 * 2 ^ 5 :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx)
  exact lt_of_le_of_lt hle (by decide)

theorem c12_wots_addIdxShl5_lt67 (base idx : Nat)
    (hbase : base ≤ 0x80) (hidx : idx < 67) :
    base + (idx <<< 5) < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : base + idx * 2 ^ 5 ≤ 128 + 66 * 2 ^ 5 :=
    Nat.add_le_add hbase (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx))
  exact lt_of_le_of_lt hle (by decide)

theorem evalC12WotsOffset (s : RuntimeState) (base idx : Nat)
    (hbase : base ≤ 0x80) (hidx : idx < 67) :
    evalExpr [] { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      (addE (u base) (shlE (u 5) (v "i"))) = some (base + 32 * idx) := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have h5 : evalExpr [] st (u 5) = some 5 := by
    show some (wordNormalize 5) = some 5
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hi : evalExpr [] st (v "i") = some idx := by
    show some (lookupValue (bindValue s.bindings "i" (wordNormalize idx)) "i") = some idx
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
      c12_wots_idxNorm67 idx hidx]
  have hsh : evalExpr [] st (shlE (u 5) (v "i")) = some (idx <<< 5) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded st (u 5) (v "i")
      5 idx h5 hi (by decide) (lt_trans hidx (by decide))
      (c12_wots_idxShl5_lt67 idx hidx)
  have hbaseLit : evalExpr [] st (u base) = some base := by
    show some (wordNormalize base) = some base
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (lt_of_le_of_lt hbase (by decide))]
  have hadd := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded st (u base)
    (shlE (u 5) (v "i")) base (idx <<< 5) hbaseLit hsh
    (lt_of_le_of_lt hbase (by decide)) (c12_wots_idxShl5_lt67 idx hidx)
    (c12_wots_addIdxShl5_lt67 base idx hbase hidx)
  convert hadd using 1
  rw [Nat.shiftLeft_eq]
  ring_nf

theorem evalC12WotsOffset_of_lookup (s : RuntimeState) (base idx : Nat)
    (hbase : base ≤ 0x80) (hidx : idx < 67)
    (hi : lookupValue s.bindings "i" = idx) :
    evalExpr [] s (addE (u base) (shlE (u 5) (v "i"))) =
      some (base + 32 * idx) := by
  have h5 : evalExpr [] s (u 5) = some 5 := by rfl
  have hiEval : evalExpr [] s (v "i") = some idx := by
    show some (lookupValue s.bindings "i") = some idx
    rw [hi]
  have hsh : evalExpr [] s (shlE (u 5) (v "i")) = some (idx <<< 5) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded s (u 5) (v "i")
      5 idx h5 hiEval (by decide) (lt_trans hidx (by decide))
      (c12_wots_idxShl5_lt67 idx hidx)
  have hbaseLit : evalExpr [] s (u base) = some base := by
    show some (wordNormalize base) = some base
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (lt_of_le_of_lt hbase (by decide))]
  have hadd := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded s (u base)
    (shlE (u 5) (v "i")) base (idx <<< 5) hbaseLit hsh
    (lt_of_le_of_lt hbase (by decide)) (c12_wots_idxShl5_lt67 idx hidx)
    (c12_wots_addIdxShl5_lt67 base idx hbase hidx)
  convert hadd using 1
  rw [Nat.shiftLeft_eq]
  ring_nf

/-- `sub(a, b)` evaluates to `k - l` when `a ↦ k`, `b ↦ l`, both `< 2^256`, and
`l ≤ k` (so EVM's `Uint256.sub` takes its non-wrapping `if`-branch).  Mirrors
`evalExpr_add_bounded` but for subtraction; the `l ≤ k` hypothesis is the WOTS
chain's `digit ≤ 7` (`subE (u 7) (v "digit")`) shape. -/
theorem evalExpr_sub_le_bounded
    (st : RuntimeState) (a b : Expr) (k l : Nat)
    (ha : evalExpr [] st a = some k) (hb : evalExpr [] st b = some l)
    (hk : k < 2 ^ 256) (hl : l < 2 ^ 256) (hle : l ≤ k) :
    evalExpr [] st (.sub a b) = some (k - l) := by
  show (do
        let lhs : Verity.Core.Uint256 := ← evalExpr [] st a
        let rhs : Verity.Core.Uint256 := ← evalExpr [] st b
        pure (lhs - rhs).val) = some (k - l)
  rw [ha, hb]
  show some ((Verity.Core.Uint256.ofNat k - Verity.Core.Uint256.ofNat l).val)
    = some (k - l)
  have hkv : (Verity.Core.Uint256.ofNat k).val = k := Nat.mod_eq_of_lt hk
  have hlv : (Verity.Core.Uint256.ofNat l).val = l := Nat.mod_eq_of_lt hl
  show some (Verity.Core.Uint256.sub
      (Verity.Core.Uint256.ofNat k) (Verity.Core.Uint256.ofNat l)).val =
    some (k - l)
  unfold Verity.Core.Uint256.sub
  rw [hkv, hlv, if_pos hle]
  show some (Verity.Core.Uint256.ofNat (k - l)).val = some (k - l)
  have hsub : (Verity.Core.Uint256.ofNat (k - l)).val = k - l :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le k l) hk)
  exact congrArg some hsub

/-- The C12 WOTS `subE (u 7) (v "digit")` shape evaluates to `7 - digit` when
the `"digit"` binding holds a 3-bit value (`digit ≤ 7`). -/
theorem evalExpr_subE_7_v_digit
    (st : RuntimeState) (digit : Nat)
    (hDigit : lookupValue st.bindings "digit" = digit) (hDigitLe : digit ≤ 7) :
    evalExpr [] st (subE (u 7) (v "digit")) = some (7 - digit) := by
  have h7 : evalExpr [] st (u 7) = some 7 := by
    show some (wordNormalize 7) = some 7
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hd : evalExpr [] st (v "digit") = some digit := by
    show some (lookupValue st.bindings "digit") = some digit
    rw [hDigit]
  have hDigitLt : digit < 2 ^ 256 := by
    have : (7 : Nat) < 2 ^ 256 := by decide
    omega
  exact evalExpr_sub_le_bounded st (u 7) (v "digit") 7 digit h7 hd
    (by decide) hDigitLt hDigitLe

/-- The C12 WOTS message-body `letVar "steps" (subE (u 7) (v "digit"))`
statement steps the state by binding `"steps"` to `7 - digit`, under the
3-bit-digit hypothesis. -/
theorem execStmt_letVar_steps_eq
    (st : RuntimeState) (digit : Nat)
    (hDigit : lookupValue st.bindings "digit" = digit) (hDigitLe : digit ≤ 7) :
    execStmt [] st (.letVar "steps" (subE (u 7) (v "digit"))) =
      .continue
        { st with bindings := bindValue st.bindings "steps" (7 - digit) } :=
  SphincsMinusVerifiers.MemoryKit.execStmt_letVar_continue
    st "steps" (subE (u 7) (v "digit")) (7 - digit)
    (evalExpr_subE_7_v_digit st digit hDigit hDigitLe)

/-- The C12 WOTS message-body `assignVar "csum"` RHS
`addE (v "csum") (subE (u 7) (v "digit"))` evaluates to `csum + (7 - digit)`
when `"csum" ↦ csum`, `"digit" ↦ digit ≤ 7`, and the sum stays `< 2^256`.
Composes `evalExpr_subE_7_v_digit` with `ClimbKeccakStep.evalExpr_add_bounded`. -/
theorem evalExpr_csum_add_subE_eq
    (st : RuntimeState) (csum digit : Nat)
    (hCsum : lookupValue st.bindings "csum" = csum)
    (hDigit : lookupValue st.bindings "digit" = digit)
    (hDigitLe : digit ≤ 7)
    (hCsumLt : csum < 2 ^ 256)
    (hSumLt : csum + (7 - digit) < 2 ^ 256) :
    evalExpr [] st (addE (v "csum") (subE (u 7) (v "digit"))) =
      some (csum + (7 - digit)) := by
  have hCsumEval : evalExpr [] st (v "csum") = some csum := by
    show some (lookupValue st.bindings "csum") = some csum
    rw [hCsum]
  have hSubEval : evalExpr [] st (subE (u 7) (v "digit")) = some (7 - digit) :=
    evalExpr_subE_7_v_digit st digit hDigit hDigitLe
  have hSubLt : 7 - digit < 2 ^ 256 := by
    have h7 : (7 : Nat) < 2 ^ 256 := by decide
    omega
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
    st (v "csum") (subE (u 7) (v "digit")) csum (7 - digit)
    hCsumEval hSubEval hCsumLt hSubLt hSumLt

/-- The C12 WOTS message-body `assignVar "csum"` statement updates the
`"csum"` binding to `csum + (7 - digit)`, under the 3-bit-digit hypothesis and
no-overflow bound. -/
theorem execStmt_assignVar_csum_eq
    (st : RuntimeState) (csum digit : Nat)
    (hCsum : lookupValue st.bindings "csum" = csum)
    (hDigit : lookupValue st.bindings "digit" = digit)
    (hDigitLe : digit ≤ 7)
    (hCsumLt : csum < 2 ^ 256)
    (hSumLt : csum + (7 - digit) < 2 ^ 256) :
    execStmt [] st (.assignVar "csum" (addE (v "csum") (subE (u 7) (v "digit")))) =
      .continue
        { st with bindings := bindValue st.bindings "csum" (csum + (7 - digit)) } :=
  assignVar_continue st "csum" (addE (v "csum") (subE (u 7) (v "digit")))
    (csum + (7 - digit))
    (evalExpr_csum_add_subE_eq st csum digit hCsum hDigit hDigitLe hCsumLt hSumLt)

/-- The C12 WOTS message-body `letVar "chainBase"` RHS
`orE (v "wotsBase") (shlE (u 64) (v "i"))` evaluates to
`wotsBase ||| (i <<< 64)` when both operands are in range and the shift does
not overflow.  Composes `ClimbKeccakStep.evalExpr_shl_bounded` for the shift
with `evalExpr_bitOr_bounded` for the final disjunction. -/
theorem evalExpr_chainBase_eq
    (st : RuntimeState) (wotsBase i : Nat)
    (hWBase : lookupValue st.bindings "wotsBase" = wotsBase)
    (hI : lookupValue st.bindings "i" = i)
    (hWBaseLt : wotsBase < 2 ^ 256) (hILt : i < 2 ^ 256)
    (hShiftLt : i <<< 64 < 2 ^ 256) :
    evalExpr [] st (orE (v "wotsBase") (shlE (u 64) (v "i"))) =
      some (wotsBase ||| (i <<< 64)) := by
  have h64 : evalExpr [] st (u 64) = some 64 := by
    show some (wordNormalize 64) = some 64
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hWBaseEval : evalExpr [] st (v "wotsBase") = some wotsBase := by
    show some (lookupValue st.bindings "wotsBase") = some wotsBase
    rw [hWBase]
  have hIEval : evalExpr [] st (v "i") = some i := by
    show some (lookupValue st.bindings "i") = some i
    rw [hI]
  have hShl : evalExpr [] st (shlE (u 64) (v "i")) = some (i <<< 64) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (u 64) (v "i") 64 i h64 hIEval (by decide) hILt hShiftLt
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
    st (v "wotsBase") (shlE (u 64) (v "i")) wotsBase (i <<< 64)
    hWBaseEval hShl hWBaseLt hShiftLt

/-- The C12 WOTS message-body `letVar "chainBase"` statement steps the state
by binding `"chainBase"` to `wotsBase ||| (i <<< 64)`, under the bounds
needed by the constituent `shl` and `bitOr` evaluators. -/
theorem execStmt_letVar_chainBase_eq
    (st : RuntimeState) (wotsBase i : Nat)
    (hWBase : lookupValue st.bindings "wotsBase" = wotsBase)
    (hI : lookupValue st.bindings "i" = i)
    (hWBaseLt : wotsBase < 2 ^ 256) (hILt : i < 2 ^ 256)
    (hShiftLt : i <<< 64 < 2 ^ 256) :
    execStmt [] st (.letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))) =
      .continue
        { st with bindings :=
            bindValue st.bindings "chainBase" (wotsBase ||| (i <<< 64)) } :=
  SphincsMinusVerifiers.MemoryKit.execStmt_letVar_continue
    st "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
    (wotsBase ||| (i <<< 64))
    (evalExpr_chainBase_eq st wotsBase i hWBase hI hWBaseLt hILt hShiftLt)

/-- The C12 WOTS message-body `letVar "val"` RHS
`andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)` evaluates
to `maskN raw` when the inner `cdload` resolves to `raw < 2^256`.  The
calldata correspondence (which calldata word `raw` is) is left as the explicit
hypothesis `hcdload`; the masking step is routed through
`ClimbKeccakStep.evalExpr_maskedCalldata`. -/
theorem evalExpr_val_calldata_mask_eq
    (st : RuntimeState) (raw : Nat)
    (hcdload : evalExpr [] st
        (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw)
    (hraw : raw < 2 ^ 256) :
    evalExpr [] st
        (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)) =
      some (SphincsMinusVerifierSpec.C13Concrete.maskN raw) :=
  SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_maskedCalldata
    st (addE (v "wotsPtr") (shlE (u 4) (v "i"))) raw hcdload hraw

/-- The C12 WOTS message-body `letVar "val"` statement steps the state by
binding `"val"` to `maskN raw`, given the calldata-load value as an explicit
hypothesis.  Companion of `evalExpr_val_calldata_mask_eq`. -/
theorem execStmt_letVar_val_eq
    (st : RuntimeState) (raw : Nat)
    (hcdload : evalExpr [] st
        (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw)
    (hraw : raw < 2 ^ 256) :
    execStmt [] st
        (.letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))) =
      .continue
        { st with bindings := (bindValue st.bindings "val"
            (SphincsMinusVerifierSpec.C13Concrete.maskN raw)) } :=
  SphincsMinusVerifiers.MemoryKit.execStmt_letVar_continue
    st "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
    (SphincsMinusVerifierSpec.C13Concrete.maskN raw)
    (evalExpr_val_calldata_mask_eq st raw hcdload hraw)

/-- `mul(a, b)` evaluates to `k * l` when `a ↦ k`, `b ↦ l`, both `< 2^256`, and
the product still `< 2^256`.  Mirrors `evalExpr_add_bounded` but for
multiplication; needed for the WOTS `letVar "digit"`'s `mulE (u 3) (v "i")`
inner term. -/
theorem evalExpr_mul_bounded
    (st : RuntimeState) (a b : Expr) (k l : Nat)
    (ha : evalExpr [] st a = some k) (hb : evalExpr [] st b = some l)
    (hk : k < 2 ^ 256) (hl : l < 2 ^ 256) (hprod : k * l < 2 ^ 256) :
    evalExpr [] st (.mul a b) = some (k * l) := by
  show (do
        let lhs : Verity.Core.Uint256 := ← evalExpr [] st a
        let rhs : Verity.Core.Uint256 := ← evalExpr [] st b
        pure (lhs * rhs).val) = some (k * l)
  rw [ha, hb]
  show some ((Verity.Core.Uint256.ofNat k * Verity.Core.Uint256.ofNat l).val)
    = some (k * l)
  show some (((Verity.Core.Uint256.ofNat k).val * (Verity.Core.Uint256.ofNat l).val)
        % Verity.Core.Uint256.modulus) = some (k * l)
  have hkv : (Verity.Core.Uint256.ofNat k).val = k := Nat.mod_eq_of_lt hk
  have hlv : (Verity.Core.Uint256.ofNat l).val = l := Nat.mod_eq_of_lt hl
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [hkv, hlv, hmod, Nat.mod_eq_of_lt hprod]

/-- The C12 WOTS message-body `letVar "digit"` RHS
`andE (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) (u 7)`
evaluates to `(currentNode >>> (128 + 3*i)) &&& 7` under the WOTS shape's
bounds.  Composes `evalExpr_mul_bounded` for `3 * i`, then
`evalExpr_add_bounded` for `128 + 3*i`, then `evalExpr_shr_bounded` for
`currentNode >>> (128 + 3*i)`, then `evalExpr_bitAnd_literal` for the final
`&&& 7`. -/
theorem evalExpr_digit_eq
    (st : RuntimeState) (i currentNode : Nat)
    (hI : lookupValue st.bindings "i" = i)
    (hCN : lookupValue st.bindings "currentNode" = currentNode)
    (hILt : i < 2 ^ 256) (hCNLt : currentNode < 2 ^ 256)
    (hMulLt : 3 * i < 2 ^ 256) (hShiftLt : 128 + 3 * i < 2 ^ 256) :
    evalExpr [] st
        (andE (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) (u 7)) =
      some ((currentNode >>> (128 + 3 * i)) &&& 7) := by
  have h3 : evalExpr [] st (u 3) = some 3 := by
    show some (wordNormalize 3) = some 3
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have h128 : evalExpr [] st (u 128) = some 128 := by
    show some (wordNormalize 128) = some 128
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hIEval : evalExpr [] st (v "i") = some i := by
    show some (lookupValue st.bindings "i") = some i
    rw [hI]
  have hCNEval : evalExpr [] st (v "currentNode") = some currentNode := by
    show some (lookupValue st.bindings "currentNode") = some currentNode
    rw [hCN]
  have hMul : evalExpr [] st (mulE (u 3) (v "i")) = some (3 * i) :=
    evalExpr_mul_bounded st (u 3) (v "i") 3 i h3 hIEval (by decide) hILt hMulLt
  have hAdd : evalExpr [] st (addE (u 128) (mulE (u 3) (v "i"))) =
      some (128 + 3 * i) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st (u 128) (mulE (u 3) (v "i")) 128 (3 * i) h128 hMul
      (by decide) hMulLt hShiftLt
  have hShr : evalExpr [] st
      (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) =
      some (currentNode >>> (128 + 3 * i)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      st (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")
      (128 + 3 * i) currentNode hAdd hCNEval hShiftLt hCNLt
  have hShrLt : currentNode >>> (128 + 3 * i) < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.shiftRight_le currentNode (128 + 3 * i)) hCNLt
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
    st (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode"))
    (currentNode >>> (128 + 3 * i)) 7 hShr hShrLt (by decide)

/-- The 3-bit-digit mask invariant: `x &&& 7 ≤ 7`. Used to discharge the
`hDigitLe` precondition consumed by `evalExpr_subE_7_v_digit` / the csum step. -/
theorem and_seven_le_seven (x : Nat) : x &&& 7 ≤ 7 := Nat.and_le_right

/-- The C12 WOTS message-body `letVar "digit"` statement steps the state by
binding `"digit"` to `(currentNode >>> (128 + 3*i)) &&& 7`. -/
theorem execStmt_letVar_digit_eq
    (st : RuntimeState) (i currentNode : Nat)
    (hI : lookupValue st.bindings "i" = i)
    (hCN : lookupValue st.bindings "currentNode" = currentNode)
    (hILt : i < 2 ^ 256) (hCNLt : currentNode < 2 ^ 256)
    (hMulLt : 3 * i < 2 ^ 256) (hShiftLt : 128 + 3 * i < 2 ^ 256) :
    execStmt [] st
        (.letVar "digit"
          (andE (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) (u 7))) =
      .continue
        { st with bindings := (bindValue st.bindings "digit"
            ((currentNode >>> (128 + 3 * i)) &&& 7)) } :=
  SphincsMinusVerifiers.MemoryKit.execStmt_letVar_continue
    st "digit"
    (andE (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) (u 7))
    ((currentNode >>> (128 + 3 * i)) &&& 7)
    (evalExpr_digit_eq st i currentNode hI hCN hILt hCNLt hMulLt hShiftLt)

/-- The C12 WOTS checksum-loop digit expression evaluates to the low three bits
of `csumShifted >>> (13 - 3*j)`. -/
theorem evalExpr_checksum_digit_eq
    (st : RuntimeState) (j csumShifted : Nat)
    (hj : j < 3)
    (hJ : lookupValue st.bindings "j" = j)
    (hCsumShifted : lookupValue st.bindings "csumShifted" = csumShifted)
    (hCsumShiftedLt : csumShifted < 2 ^ 256) :
    evalExpr [] st
        (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)) =
      some ((csumShifted >>> (13 - 3 * j)) &&& 7) := by
  have h3 : evalExpr [] st (u 3) = some 3 := by
    show some (wordNormalize 3) = some 3
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have h13 : evalExpr [] st (u 13) = some 13 := by
    show some (wordNormalize 13) = some 13
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hJEval : evalExpr [] st (v "j") = some j := by
    show some (lookupValue st.bindings "j") = some j
    rw [hJ]
  have hCsumEval : evalExpr [] st (v "csumShifted") = some csumShifted := by
    show some (lookupValue st.bindings "csumShifted") = some csumShifted
    rw [hCsumShifted]
  have hJLt : j < 2 ^ 256 := lt_trans hj (by decide)
  have hMulLt : 3 * j < 2 ^ 256 := by
    have hle : 3 * j ≤ 3 * 2 := Nat.mul_le_mul_left _ (by omega)
    have hsmall : (3 : Nat) * 2 < 2 ^ 256 := by decide
    omega
  have hMulEval : evalExpr [] st (mulE (u 3) (v "j")) = some (3 * j) :=
    evalExpr_mul_bounded st (u 3) (v "j") 3 j h3 hJEval
      (by decide) hJLt hMulLt
  have hSubEval :
      evalExpr [] st (subE (u 13) (mulE (u 3) (v "j"))) =
        some (13 - 3 * j) := by
    exact evalExpr_sub_le_bounded st (u 13) (mulE (u 3) (v "j"))
      13 (3 * j) h13 hMulEval (by decide) hMulLt (by omega)
  have hShiftLt : 13 - 3 * j < 2 ^ 256 := by
    omega
  have hShr : evalExpr [] st
      (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) =
      some (csumShifted >>> (13 - 3 * j)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      st (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")
      (13 - 3 * j) csumShifted hSubEval hCsumEval hShiftLt hCsumShiftedLt
  have hShrLt : csumShifted >>> (13 - 3 * j) < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.shiftRight_le csumShifted (13 - 3 * j)) hCsumShiftedLt
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
    st (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted"))
    (csumShifted >>> (13 - 3 * j)) 7 hShr hShrLt (by decide)

/-- `chainHashC12` lands in `[0, 2^256)` whenever its input `val` is in the same
range.  Base case is by definition (the `fuel = 0` branch returns `val`); step
case relies on `Nat.bitwise_lt_two_pow` applied to the keccak-words preimage
(bounded by `KeccakBridge.keccakWords_lt`) and `nMask` (bounded by
`ClimbKeccakStep.nMask_lt`). -/
private theorem chainHashC12_lt_two_pow
    (seed chainBase digit : Nat) :
    ∀ (fuel step val : Nat), val < 2 ^ 256 →
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
        fuel step val < 2 ^ 256
  | 0, _, val, hval => hval
  | f + 1, step, val, _hval => by
      unfold SphincsMinusVerifierSpec.C12Concrete.chainHashC12
      apply chainHashC12_lt_two_pow seed chainBase digit f (step + 1)
      show Nat.bitwise and _ SphincsMinusVerifierSpec.C13Concrete.nMask < 2 ^ 256
      apply Nat.bitwise_lt_two_pow
      · have := SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
          [seed, chainBase ||| ((digit + step) <<< 32), val]
        rwa [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl] at this
      · exact SphincsMinusVerifiers.ClimbKeccakStep.nMask_lt

/-- The "chain tail" of one WOTS message-loop iteration — the inner
`forEach "s"` over `c12WotsChainBody` followed by the final
`mstore (0x80 + 32*i)` of `"val"` — writes
`chainHashC12 seed chainBase digit (7 - digit) 0 val0` into memory cell
`0x80 + 32 * i`.

The state pre-conditions encode the executable invariant after the WOTS
message body has set the per-iteration bindings (`digit`, `steps`, `chainBase`,
`val` from calldata) but before running the chain loop and the per-iteration
mstore.  This is the executable-semantics bridge M3c uses to pin one full
message-loop iteration to its `chainHashC12` slot. -/
theorem c12WotsMessage_chainTail_mem_at_i
    (st : RuntimeState) (i seed chainBase digit val0 : Nat) (hi : i < 67)
    (hCBlt : chainBase < 2 ^ 256) (hDigitLe : digit ≤ 7)
    (hVal0Lt : val0 < 2 ^ 256)
    (hSeed : (st.world.memory 0x00).val = seed)
    (hI : lookupValue st.bindings "i" = i)
    (hCB : lookupValue st.bindings "chainBase" = chainBase)
    (hDigit : lookupValue st.bindings "digit" = digit)
    (hSteps : lookupValue st.bindings "steps" = 7 - digit)
    (hVal : lookupValue st.bindings "val" = val0) :
    ∃ s', execStmtList [] st
      [ .forEach "s" (v "steps") c12WotsChainBody
      , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ] = .continue s'
    ∧ (s'.world.memory (0x80 + 32 * i)).val =
        SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
          (7 - digit) 0 val0 := by
  -- Concrete witnesses for the loop and final states
  set stInit : RuntimeState :=
    { st with bindings := bindValue st.bindings "s" (wordNormalize 0) } with hStInit
  set sLoop : RuntimeState :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop "s" c12WotsChainStep stInit 0 (7 - digit)
    with hSLoop
  let sFinal : RuntimeState :=
    { sLoop with world :=
        { sLoop.world with
          memory := SphincsMinusVerifiers.MemoryKit.memUpdate sLoop.world.memory
            (0x80 + 32 * i)
            (SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
              (7 - digit) 0 val0) } }
  -- Step 1: forEach evaluates to a foldLoop over the chain-step
  have hSteps_eval : evalExpr [] st (v "steps") = some (7 - digit) := by
    show some (lookupValue st.bindings "steps") = some (7 - digit)
    rw [hSteps]
  have hForEach : execStmt [] st (.forEach "s" (v "steps") c12WotsChainBody) =
      .continue sLoop :=
    SphincsMinusVerifiers.ClimbLoop.execStmt_forEach_of_step
      "s" (v "steps") c12WotsChainBody st (7 - digit) c12WotsChainStep
      hSteps_eval execC12WotsChainBody
  -- Step 2: hypotheses on stInit for M3b
  have hCB_b : lookupValue stInit.bindings "chainBase" = chainBase := by
    show lookupValue (bindValue st.bindings "s" (wordNormalize 0)) "chainBase" =
      chainBase
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "s" "chainBase" _ (by decide)]
    exact hCB
  have hDigit_b : lookupValue stInit.bindings "digit" = digit := by
    show lookupValue (bindValue st.bindings "s" (wordNormalize 0)) "digit" = digit
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "s" "digit" _ (by decide)]
    exact hDigit
  have hVal_b : lookupValue stInit.bindings "val" = val0 := by
    show lookupValue (bindValue st.bindings "s" (wordNormalize 0)) "val" = val0
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "s" "val" _ (by decide)]
    exact hVal
  have hI_b : lookupValue stInit.bindings "i" = i := by
    show lookupValue (bindValue st.bindings "s" (wordNormalize 0)) "i" = i
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "s" "i" _ (by decide)]
    exact hI
  have hMemB : (stInit.world.memory 0x00).val = seed := hSeed
  have hValLt_b : lookupValue stInit.bindings "val" < 2 ^ 256 := by
    rw [hVal_b]; exact hVal0Lt
  have hSum_b : 0 + (7 - digit) ≤ 7 := by omega
  -- Step 3: "val" after the foldLoop = chainHashC12-result
  have hValChain : lookupValue sLoop.bindings "val" =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
        (7 - digit) 0 val0 := by
    have hIH := c12WotsChain_foldLoop_val_eq seed chainBase digit hCBlt hDigitLe
      stInit 0 (7 - digit) hMemB hCB_b hDigit_b hValLt_b hSum_b
    show lookupValue
      (SphincsMinusVerifiers.ClimbLoop.foldLoop "s" c12WotsChainStep stInit 0
        (7 - digit)).bindings "val" = _
    rw [hIH, hVal_b]
  -- Step 4: "i" preserved through the foldLoop
  have hI_loop : lookupValue sLoop.bindings "i" = i := by
    show lookupValue
      (SphincsMinusVerifiers.ClimbLoop.foldLoop "s" c12WotsChainStep stInit 0
        (7 - digit)).bindings "i" = i
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup "s" "i"
      c12WotsChainStep (by decide)
      (fun s => c12WotsChainStep_preserves_lookup_of_ne_val "i" (by decide) s)
      stInit 0 (7 - digit)]
    exact hI_b
  -- Step 5: evaluate the mstore offset
  have hOff : evalExpr [] sLoop (addE (u 0x80) (shlE (u 5) (v "i"))) =
      some (0x80 + 32 * i) :=
    evalC12WotsOffset_of_lookup sLoop 0x80 i (by decide) (by omega) hI_loop
  -- Step 6: evaluate the mstore value
  have hValExpr : evalExpr [] sLoop (v "val") = some
      (SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
        (7 - digit) 0 val0) := by
    show some (lookupValue sLoop.bindings "val") = _
    rw [hValChain]
  -- Step 7: mstore step → sFinal
  have hMstore : execStmt [] sLoop
      (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) =
      .continue sFinal := by
    unfold mstoreE
    exact SphincsMinusVerifiers.MemoryKit.execStmt_mstore_continue sLoop
      (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") (0x80 + 32 * i)
      (SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
        (7 - digit) 0 val0)
      hOff hValExpr
  -- Step 8: existential intro with explicit witness sFinal
  refine ⟨sFinal, ?_, ?_⟩
  · rw [execStmtList_cons_continue _ _ _ _ hForEach]
    rw [execStmtList_cons_continue _ _ _ _ hMstore]
    rfl
  · -- (sFinal.world.memory (0x80 + 32 * i)).val = chainHashC12-result
    show (SphincsMinusVerifiers.MemoryKit.memUpdate sLoop.world.memory
        (0x80 + 32 * i)
        (SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
          (7 - digit) 0 val0) (0x80 + 32 * i)).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
        (7 - digit) 0 val0
    rw [SphincsMinusVerifiers.MemoryKit.memUpdate_val_same,
      wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (chainHashC12_lt_two_pow seed chainBase digit
        (7 - digit) 0 val0 hVal0Lt)]

/-- One full `c12WotsMessageStep` iteration writes
`chainHashC12 seed chainBase digit (7 - digit) 0 val0` into memory cell
`0x80 + 32*i`, *given* a witness `state5` that the five preceding statements
of `c12WotsMessageBody` (the per-iteration setup before the chain loop and
final `mstore`) have already been executed into a state where the chain-loop
bindings are correct.

This factors the message-step semantics around the chain-tail bridge
`c12WotsMessage_chainTail_mem_at_i`: the caller supplies the 5-statement
prefix execution result (which evaluates `"digit"`, `"csum"`, `"val"`,
`"chainBase"`, `"steps"`), and this lemma stitches it onto the chain-loop +
mstore tail.  The prefix can be discharged later by a separate executable-
semantics lemma for the 5 letVar/assignVar statements; this lemma keeps that
work separable. -/
theorem c12WotsMessageStep_mem_at_i_via_prefix5
    (st state5 : RuntimeState) (i seed chainBase digit val0 : Nat) (hi : i < 42)
    (hCBlt : chainBase < 2 ^ 256) (hDigitLe : digit ≤ 7)
    (hVal0Lt : val0 < 2 ^ 256)
    (hPrefix5 : execStmtList [] st
      [ .letVar "digit"
          (andE (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) (u 7))
      , .assignVar "csum" (addE (v "csum") (subE (u 7) (v "digit")))
      , .letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
      , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
      , .letVar "steps" (subE (u 7) (v "digit"))
      ] = .continue state5)
    (hMem5 : (state5.world.memory 0x00).val = seed)
    (hI5 : lookupValue state5.bindings "i" = i)
    (hCB5 : lookupValue state5.bindings "chainBase" = chainBase)
    (hDigit5 : lookupValue state5.bindings "digit" = digit)
    (hSteps5 : lookupValue state5.bindings "steps" = 7 - digit)
    (hVal5 : lookupValue state5.bindings "val" = val0) :
    ((c12WotsMessageStep st).world.memory (0x80 + 32 * i)).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
        (7 - digit) 0 val0 := by
  -- M3c-tail: ∃ s', execStmtList [forEach, mstore] from state5 = .continue s'
  --   with (s'.world.memory (0x80+32*i)).val = chainHashC12-result
  obtain ⟨sFinal, hExecTail, hMemFinal⟩ :=
    c12WotsMessage_chainTail_mem_at_i state5 i seed chainBase digit val0 (by omega)
      hCBlt hDigitLe hVal0Lt hMem5 hI5 hCB5 hDigit5 hSteps5 hVal5
  -- c12WotsMessageBody = prefix5 ++ [forEach, mstoreE]
  have hBody : c12WotsMessageBody =
      [ .letVar "digit"
          (andE (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) (u 7))
      , .assignVar "csum" (addE (v "csum") (subE (u 7) (v "digit")))
      , .letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
      , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
      , .letVar "steps" (subE (u 7) (v "digit")) ] ++
      [ .forEach "s" (v "steps") c12WotsChainBody
      , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ] := rfl
  -- Compose prefix5 with the tail through execStmtList_append_continue
  have hExecBody : execStmtList [] st c12WotsMessageBody = .continue sFinal := by
    rw [hBody,
      SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue _ _ _ _ hPrefix5]
    exact hExecTail
  -- Unfold c12WotsMessageStep and conclude
  show ((c12WotsMessageStep st).world.memory (0x80 + 32 * i)).val =
    SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed chainBase digit
      (7 - digit) 0 val0
  unfold c12WotsMessageStep
  rw [hExecBody]
  exact hMemFinal

set_option maxHeartbeats 600000 in
/-- One full `c12WotsMessageStep` iteration writes
`chainHashC12 seed (wotsBase ||| (i <<< 64)) digit (7 - digit) 0 (maskN raw)`
into memory cell `0x80 + 32*i`, where `digit = (currentNode >>> (128 + 3*i)) &&& 7`
and `raw` is the calldata word at `wotsPtr + 16*i`.

Discharges the `hPrefix5` hypothesis of `c12WotsMessageStep_mem_at_i_via_prefix5`
by composing the five `execStmt_*_eq` lemmas for `letVar "digit"`,
`assignVar "csum"`, `letVar "val"`, `letVar "chainBase"`, `letVar "steps"`,
threading `bindValue` lookup-preservation across the four mismatched keys at
each intermediate state.  The calldata correspondence is left as the
`hCdLoad` hypothesis, instantiated at the post-stmt-2 state via
world-equality. -/
theorem c12WotsMessageStep_mem_at_i_eq
    (st : RuntimeState) (i seed currentNode csum wotsBase wotsPtr raw : Nat)
    (hi : i < 42)
    (hCNLt : currentNode < 2 ^ 256) (hWBaseLt : wotsBase < 2 ^ 256)
    (hCsumLt : csum + 7 < 2 ^ 256) (hRaw : raw < 2 ^ 256)
    (hSeed : (st.world.memory 0x00).val = seed)
    (hI : lookupValue st.bindings "i" = i)
    (hCN : lookupValue st.bindings "currentNode" = currentNode)
    (hCsum : lookupValue st.bindings "csum" = csum)
    (hWBase : lookupValue st.bindings "wotsBase" = wotsBase)
    (hWPtr : lookupValue st.bindings "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = i →
        s.world = st.world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw) :
    ((c12WotsMessageStep st).world.memory (0x80 + 32 * i)).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
        (wotsBase ||| (i <<< 64))
        ((currentNode >>> (128 + 3 * i)) &&& 7)
        (7 - ((currentNode >>> (128 + 3 * i)) &&& 7)) 0
        (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := by
  -- Bounds derived from i < 42
  have hILt : i < 2 ^ 256 := lt_trans hi (by decide)
  have hMulLt : 3 * i < 2 ^ 256 := by
    have h1 : 3 * i ≤ 3 * 41 := Nat.mul_le_mul_left _ (by omega)
    have h2 : (3 : Nat) * 41 < 2 ^ 256 := by decide
    omega
  have hShiftLt : 128 + 3 * i < 2 ^ 256 := by
    have h1 : 128 + 3 * i ≤ 128 + 3 * 41 := by omega
    have h2 : (128 : Nat) + 3 * 41 < 2 ^ 256 := by decide
    omega
  have hShlLt : i <<< 64 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have h1 : i * 2 ^ 64 ≤ 41 * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
    have h2 : (41 : Nat) * 2 ^ 64 < 2 ^ 256 := by decide
    omega
  have hDigitLe : ((currentNode >>> (128 + 3 * i)) &&& 7) ≤ 7 :=
    and_seven_le_seven _
  have hCsumLt' : csum < 2 ^ 256 := by omega
  have hSumLt : csum + (7 - ((currentNode >>> (128 + 3 * i)) &&& 7)) < 2 ^ 256 := by
    have hle : 7 - ((currentNode >>> (128 + 3 * i)) &&& 7) ≤ 7 := by omega
    omega
  -- Step 1: letVar "digit"
  have hStep1 := execStmt_letVar_digit_eq st i currentNode hI hCN hILt hCNLt
    hMulLt hShiftLt
  -- The post-stmt1 state
  let state1 : RuntimeState :=
    { st with bindings := (bindValue st.bindings "digit"
        ((currentNode >>> (128 + 3 * i)) &&& 7)) }
  -- Lookups at state1
  have hCsum1 : lookupValue state1.bindings "csum" = csum := by
    show lookupValue (bindValue st.bindings "digit" _) "csum" = csum
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "digit" "csum" _ (by decide)]
    exact hCsum
  have hDigit1 : lookupValue state1.bindings "digit" =
      (currentNode >>> (128 + 3 * i)) &&& 7 := by
    show lookupValue (bindValue st.bindings "digit" _) "digit" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  -- Step 2: assignVar "csum"
  have hStep2 := execStmt_assignVar_csum_eq state1 csum
    ((currentNode >>> (128 + 3 * i)) &&& 7)
    hCsum1 hDigit1 hDigitLe hCsumLt' hSumLt
  -- The post-stmt2 state
  let state2 : RuntimeState :=
    { state1 with bindings := (bindValue state1.bindings "csum"
        (csum + (7 - ((currentNode >>> (128 + 3 * i)) &&& 7)))) }
  -- Lookups at state2
  have hWPtr2 : lookupValue state2.bindings "wotsPtr" = wotsPtr := by
    show lookupValue (bindValue _ "csum" _) "wotsPtr" = wotsPtr
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "csum" "wotsPtr" _ (by decide)]
    show lookupValue (bindValue st.bindings "digit" _) "wotsPtr" = wotsPtr
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "digit" "wotsPtr" _ (by decide)]
    exact hWPtr
  have hI2 : lookupValue state2.bindings "i" = i := by
    show lookupValue (bindValue _ "csum" _) "i" = i
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "csum" "i" _ (by decide)]
    show lookupValue (bindValue st.bindings "digit" _) "i" = i
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "digit" "i" _ (by decide)]
    exact hI
  have hWorld2 : state2.world = st.world := rfl
  have hcdload2 := hCdLoad state2 hWPtr2 hI2 hWorld2
  -- Step 3: letVar "val"
  have hStep3 := execStmt_letVar_val_eq state2 raw hcdload2 hRaw
  let state3 : RuntimeState :=
    { state2 with bindings := (bindValue state2.bindings "val"
        (SphincsMinusVerifierSpec.C13Concrete.maskN raw)) }
  -- Lookups at state3
  have hWBase3 : lookupValue state3.bindings "wotsBase" = wotsBase := by
    show lookupValue (bindValue _ "val" _) "wotsBase" = wotsBase
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "val" "wotsBase" _ (by decide)]
    show lookupValue (bindValue _ "csum" _) "wotsBase" = wotsBase
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "csum" "wotsBase" _ (by decide)]
    show lookupValue (bindValue st.bindings "digit" _) "wotsBase" = wotsBase
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "digit" "wotsBase" _ (by decide)]
    exact hWBase
  have hI3 : lookupValue state3.bindings "i" = i := by
    show lookupValue (bindValue _ "val" _) "i" = i
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "val" "i" _ (by decide)]
    exact hI2
  -- Step 4: letVar "chainBase"
  have hStep4 := execStmt_letVar_chainBase_eq state3 wotsBase i hWBase3 hI3
    hWBaseLt hILt hShlLt
  let state4 : RuntimeState :=
    { state3 with bindings :=
        (bindValue state3.bindings "chainBase" (wotsBase ||| (i <<< 64))) }
  -- Lookups at state4
  have hDigit4 : lookupValue state4.bindings "digit" =
      (currentNode >>> (128 + 3 * i)) &&& 7 := by
    show lookupValue (bindValue _ "chainBase" _) "digit" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "chainBase" "digit" _ (by decide)]
    show lookupValue (bindValue _ "val" _) "digit" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "val" "digit" _ (by decide)]
    show lookupValue (bindValue _ "csum" _) "digit" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "csum" "digit" _ (by decide)]
    exact hDigit1
  -- Step 5: letVar "steps"
  have hStep5 := execStmt_letVar_steps_eq state4
    ((currentNode >>> (128 + 3 * i)) &&& 7) hDigit4 hDigitLe
  let state5 : RuntimeState :=
    { state4 with bindings := (bindValue state4.bindings "steps"
        (7 - ((currentNode >>> (128 + 3 * i)) &&& 7))) }
  -- Compose execStmtList over prefix5
  have hPrefix5 : execStmtList [] st
      [ .letVar "digit"
          (andE (shrE (addE (u 128) (mulE (u 3) (v "i"))) (v "currentNode")) (u 7))
      , .assignVar "csum" (addE (v "csum") (subE (u 7) (v "digit")))
      , .letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
      , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
      , .letVar "steps" (subE (u 7) (v "digit"))
      ] = .continue state5 := by
    rw [execStmtList_cons_continue _ _ _ _ hStep1]
    rw [execStmtList_cons_continue _ _ _ _ hStep2]
    rw [execStmtList_cons_continue _ _ _ _ hStep3]
    rw [execStmtList_cons_continue _ _ _ _ hStep4]
    rw [execStmtList_cons_continue _ _ _ _ hStep5]
    rfl
  -- Derive state5 facts for c12WotsMessageStep_mem_at_i_via_prefix5
  have hMem5 : (state5.world.memory 0x00).val = seed := hSeed
  have hI5 : lookupValue state5.bindings "i" = i := by
    show lookupValue (bindValue _ "steps" _) "i" = i
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "steps" "i" _ (by decide)]
    show lookupValue (bindValue _ "chainBase" _) "i" = i
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "chainBase" "i" _ (by decide)]
    exact hI3
  have hCB5 : lookupValue state5.bindings "chainBase" =
      wotsBase ||| (i <<< 64) := by
    show lookupValue (bindValue _ "steps" _) "chainBase" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "steps" "chainBase" _ (by decide)]
    show lookupValue (bindValue _ "chainBase" _) "chainBase" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hDigit5 : lookupValue state5.bindings "digit" =
      (currentNode >>> (128 + 3 * i)) &&& 7 := by
    show lookupValue (bindValue _ "steps" _) "digit" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "steps" "digit" _ (by decide)]
    exact hDigit4
  have hSteps5 : lookupValue state5.bindings "steps" =
      7 - ((currentNode >>> (128 + 3 * i)) &&& 7) := by
    show lookupValue (bindValue _ "steps" _) "steps" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hVal5 : lookupValue state5.bindings "val" =
      SphincsMinusVerifierSpec.C13Concrete.maskN raw := by
    show lookupValue (bindValue _ "steps" _) "val" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "steps" "val" _ (by decide)]
    show lookupValue (bindValue _ "chainBase" _) "val" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "chainBase" "val" _ (by decide)]
    show lookupValue (bindValue _ "val" _) "val" = _
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  -- Bounds for c12WotsMessageStep_mem_at_i_via_prefix5
  have hChainBaseLt : wotsBase ||| (i <<< 64) < 2 ^ 256 := by
    show Nat.bitwise or wotsBase (i <<< 64) < 2 ^ 256
    exact Nat.bitwise_lt_two_pow hWBaseLt hShlLt
  have hVal0Lt : SphincsMinusVerifierSpec.C13Concrete.maskN raw < 2 ^ 256 := by
    show Nat.bitwise and raw SphincsMinusVerifierSpec.C13Concrete.nMask < 2 ^ 256
    exact Nat.bitwise_lt_two_pow hRaw
      SphincsMinusVerifiers.ClimbKeccakStep.nMask_lt
  -- Apply c12WotsMessageStep_mem_at_i_via_prefix5
  exact c12WotsMessageStep_mem_at_i_via_prefix5 st state5 i seed
    (wotsBase ||| (i <<< 64))
    ((currentNode >>> (128 + 3 * i)) &&& 7)
    (SphincsMinusVerifierSpec.C13Concrete.maskN raw)
    hi hChainBaseLt hDigitLe hVal0Lt hPrefix5 hMem5 hI5 hCB5 hDigit5 hSteps5 hVal5

set_option maxHeartbeats 600000 in
/-- Small reusable 42-message-loop invariant for one fixed message digit.

For `j < 42`, if the state just before iteration `j` has the bindings/memory
needed by `c12WotsMessageStep_mem_at_i_eq`, and every later message iteration
preserves the slot `0x80 + 32*j`, then the full 42-iteration message fold has
that slot equal to the `chainHashC12` expression for iteration `j`.

This is deliberately factored around the one remaining frame obligation
`hSuffixPreserves`: concrete non-aliasing facts for the later message steps can
discharge it without changing the invariant statement. -/
theorem c12WotsMessageLoop_mem_at_j_eq_of_suffix_preserves
    (st : RuntimeState) (j seed currentNode csum wotsBase wotsPtr raw : Nat)
    (hj : j < 42)
    (hCNLt : currentNode < 2 ^ 256) (hWBaseLt : wotsBase < 2 ^ 256)
    (hCsumLt : csum + 7 < 2 ^ 256) (hRaw : raw < 2 ^ 256)
    (hSeed :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).world.memory
        0x00).val = seed)
    (hCN :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).bindings
        "currentNode" = currentNode)
    (hCsum :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).bindings
        "csum" = csum)
    (hWBase :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).bindings
        "wotsBase" = wotsBase)
    (hWPtr :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).bindings
        "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = j →
        s.world =
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw)
    (hSuffixPreserves : ∀ (s : RuntimeState) (idx : Nat),
        j < idx → idx < 42 →
        ((c12WotsMessageStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
          (0x80 + 32 * j)).val =
          (s.world.memory (0x80 + 32 * j)).val) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 42).world.memory
      (0x80 + 32 * j)).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
        (wotsBase ||| (j <<< 64))
        ((currentNode >>> (128 + 3 * j)) &&& 7)
        (7 - ((currentNode >>> (128 + 3 * j)) &&& 7)) 0
        (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := by
  let beforeJ : RuntimeState :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j
  let atJ : RuntimeState :=
    { beforeJ with bindings := bindValue beforeJ.bindings "i" (wordNormalize j) }
  have hStepAt :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_memory_val_eq_step_at_of_suffix_preserves
      "i" c12WotsMessageStep (0x80 + 32 * j) st 0 42 j hj
      (fun s idx hgt hlt => hSuffixPreserves s idx (by omega) (by omega))
  have hIAt : lookupValue atJ.bindings "i" = j := by
    dsimp [atJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
      c12_wots_idxNorm67 j (by omega)]
  have hCNAt : lookupValue atJ.bindings "currentNode" = currentNode := by
    dsimp [atJ, beforeJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "currentNode" _ (by decide)]
    exact hCN
  have hCsumAt : lookupValue atJ.bindings "csum" = csum := by
    dsimp [atJ, beforeJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "csum" _ (by decide)]
    exact hCsum
  have hWBaseAt : lookupValue atJ.bindings "wotsBase" = wotsBase := by
    dsimp [atJ, beforeJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "wotsBase" _ (by decide)]
    exact hWBase
  have hWPtrAt : lookupValue atJ.bindings "wotsPtr" = wotsPtr := by
    dsimp [atJ, beforeJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "wotsPtr" _ (by decide)]
    exact hWPtr
  have hSeedAt : (atJ.world.memory 0x00).val = seed := by
    dsimp [atJ, beforeJ]
    exact hSeed
  have hCdLoadAt : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = j →
        s.world = atJ.world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw := by
    intro s hw hi hworld
    exact hCdLoad s hw hi (by simpa [atJ, beforeJ] using hworld)
  have hStepMem :
      ((c12WotsMessageStep atJ).world.memory (0x80 + 32 * j)).val =
        SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
          (wotsBase ||| (j <<< 64))
          ((currentNode >>> (128 + 3 * j)) &&& 7)
          (7 - ((currentNode >>> (128 + 3 * j)) &&& 7)) 0
          (SphincsMinusVerifierSpec.C13Concrete.maskN raw) :=
    c12WotsMessageStep_mem_at_i_eq atJ j seed currentNode csum wotsBase wotsPtr raw
      hj hCNLt hWBaseLt hCsumLt hRaw hSeedAt hIAt hCNAt hCsumAt hWBaseAt hWPtrAt
      hCdLoadAt
  calc
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 42).world.memory
        (0x80 + 32 * j)).val
        = ((c12WotsMessageStep
            { (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j) with
              bindings :=
                bindValue
                  (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).bindings
                  "i" (wordNormalize (0 + j)) }).world.memory
            (0x80 + 32 * j)).val := hStepAt
    _ = ((c12WotsMessageStep atJ).world.memory (0x80 + 32 * j)).val := by
      simp [atJ, beforeJ]
    _ = SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
          (wotsBase ||| (j <<< 64))
          ((currentNode >>> (128 + 3 * j)) &&& 7)
          (7 - ((currentNode >>> (128 + 3 * j)) &&& 7)) 0
          (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := hStepMem

set_option maxHeartbeats 2000000 in
theorem c12WotsMessageBody_preserves_memory_zero_bound
    (s : RuntimeState) (idx : Nat) (hidx : idx < 42) (s'' : RuntimeState)
    (hExec : execStmtList []
      { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      c12WotsMessageBody = .continue s'') :
    (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  rw [c12WotsMessageBody_eq_prefix_tail, MemoryKit.execStmtList_append] at hExec
  cases hp : execStmtList [] st c12WotsMessagePrefix with
  | «continue» mid =>
      rw [hp] at hExec
      have hprefixMem := c12WotsMessagePrefix_preserves_memory_zero st mid hp
      have hprefixI := c12WotsMessagePrefix_preserves_i st mid hp
      have hstI : lookupValue st.bindings "i" = idx := by
        dsimp [st]
        rw [MemoryKit.lookupValue_bindValue_self, c12_wots_idxNorm67 idx (by omega)]
      have hmidI : lookupValue mid.bindings "i" = idx := by
        rw [hprefixI, hstI]
      have hoff : evalExpr [] mid (addE (u 0x80) (shlE (u 5) (v "i"))) =
          some (0x80 + 32 * idx) := by
        have h5 : evalExpr [] mid (u 5) = some 5 := by rfl
        have hi : evalExpr [] mid (v "i") = some idx := by
          show some (lookupValue mid.bindings "i") = some idx
          rw [hmidI]
        have hsh : evalExpr [] mid (shlE (u 5) (v "i")) = some (idx <<< 5) :=
          SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded mid (u 5) (v "i")
            5 idx h5 hi (by decide) (lt_trans hidx (by decide))
            (c12_wots_idxShl5_lt67 idx (by omega))
        have hbase : evalExpr [] mid (u 0x80) = some 0x80 := by rfl
        have hadd := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
          mid (u 0x80) (shlE (u 5) (v "i")) 0x80 (idx <<< 5)
          hbase hsh (by decide) (c12_wots_idxShl5_lt67 idx (by omega))
          (c12_wots_addIdxShl5_lt67 0x80 idx (by decide) (by omega))
        convert hadd using 1
        rw [Nat.shiftLeft_eq]
        ring_nf
      have hval : evalExpr [] mid (v "val") = some (lookupValue mid.bindings "val") := rfl
      let out : RuntimeState :=
        { mid with world := { mid.world with
            memory := MemoryKit.memUpdate mid.world.memory (0x80 + 32 * idx)
              (lookupValue mid.bindings "val") } }
      have hstore : execStmt [] mid
          (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) =
          .continue out := by
        unfold out mstoreE
        exact execStmt_mstore_continue mid
          (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
          (0x80 + 32 * idx) (lookupValue mid.bindings "val") hoff hval
      change (match execStmt [] mid
          (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) with
        | .continue n => execStmtList [] n []
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) = .continue s'' at hExec
      rw [hstore] at hExec
      simp only [execStmtList] at hExec
      injection hExec with hs
      subst s''
      unfold out
      change (MemoryKit.memUpdate mid.world.memory (0x80 + 32 * idx)
          (lookupValue mid.bindings "val") 0x00).val =
        (s.world.memory 0x00).val
      rw [MemoryKit.memUpdate_diff _ (0x80 + 32 * idx) 0x00
        (lookupValue mid.bindings "val") (by omega)]
      exact hprefixMem
  | stop stopped => rw [hp] at hExec; simp at hExec
  | «return» rv rst => rw [hp] at hExec; simp at hExec
  | revert => rw [hp] at hExec; simp at hExec

set_option maxHeartbeats 1000000 in
theorem c12WotsMessageBody_preserves_memory_addr_of_ne_bound
    (s : RuntimeState) (idx addr : Nat) (hidx : idx < 42)
    (h20 : addr ≠ 0x20) (h40 : addr ≠ 0x40)
    (hFinal : addr ≠ 0x80 + 32 * idx) (s'' : RuntimeState)
    (hExec : execStmtList []
      { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      c12WotsMessageBody = .continue s'') :
    (s''.world.memory addr).val = (s.world.memory addr).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  rw [c12WotsMessageBody_eq_prefix_tail, MemoryKit.execStmtList_append] at hExec
  cases hp : execStmtList [] st c12WotsMessagePrefix with
  | «continue» mid =>
      rw [hp] at hExec
      have hprefixMem :=
        c12WotsMessagePrefix_preserves_memory_addr_of_ne addr h20 h40 st mid hp
      have hprefixI := c12WotsMessagePrefix_preserves_i st mid hp
      have hstI : lookupValue st.bindings "i" = idx := by
        dsimp [st]
        rw [MemoryKit.lookupValue_bindValue_self, c12_wots_idxNorm67 idx (by omega)]
      have hmidI : lookupValue mid.bindings "i" = idx := by
        rw [hprefixI, hstI]
      have hoff : evalExpr [] mid (addE (u 0x80) (shlE (u 5) (v "i"))) =
          some (0x80 + 32 * idx) :=
        evalC12WotsOffset_of_lookup mid 0x80 idx (by decide) (by omega) hmidI
      have hval : evalExpr [] mid (v "val") = some (lookupValue mid.bindings "val") := rfl
      let out : RuntimeState :=
        { mid with world := { mid.world with
            memory := MemoryKit.memUpdate mid.world.memory (0x80 + 32 * idx)
              (lookupValue mid.bindings "val") } }
      have hstore : execStmt [] mid
          (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) =
          .continue out := by
        unfold out mstoreE
        exact execStmt_mstore_continue mid
          (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
          (0x80 + 32 * idx) (lookupValue mid.bindings "val") hoff hval
      change (match execStmt [] mid
          (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) with
        | .continue n => execStmtList [] n []
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) = .continue s'' at hExec
      rw [hstore] at hExec
      simp only [execStmtList] at hExec
      injection hExec with hs
      subst s''
      unfold out
      change (MemoryKit.memUpdate mid.world.memory (0x80 + 32 * idx)
          (lookupValue mid.bindings "val") addr).val =
        (s.world.memory addr).val
      rw [MemoryKit.memUpdate_diff _ (0x80 + 32 * idx) addr
        (lookupValue mid.bindings "val") hFinal]
      exact hprefixMem
  | stop stopped => rw [hp] at hExec; simp at hExec
  | «return» rv rst => rw [hp] at hExec; simp at hExec
  | revert => rw [hp] at hExec; simp at hExec

/-- A later C12 WOTS message-loop iteration preserves an earlier message cell.
This is the concrete suffix-preservation fact needed by
`c12WotsMessageLoop_mem_at_j_eq_of_suffix_preserves`. -/
theorem c12WotsMessageStep_preserves_prior_message_cell
    (s : RuntimeState) (j idx : Nat) (hjidx : j < idx) (hidx : idx < 42) :
    ((c12WotsMessageStep
      { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
      (0x80 + 32 * j)).val =
      (s.world.memory (0x80 + 32 * j)).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  exact c12WotsMessageBody_preserves_memory_addr_of_ne_bound
    s idx (0x80 + 32 * j) hidx (by omega) (by omega) (by omega)
    (c12WotsMessageStep st) (execC12WotsMessageBody st)

set_option maxHeartbeats 600000 in
/-- Concrete fixed-cell invariant for the 42-step C12 WOTS message loop. -/
theorem c12WotsMessageLoop_mem_at_j_eq
    (st : RuntimeState) (j seed currentNode csum wotsBase wotsPtr raw : Nat)
    (hj : j < 42)
    (hCNLt : currentNode < 2 ^ 256) (hWBaseLt : wotsBase < 2 ^ 256)
    (hCsumLt : csum + 7 < 2 ^ 256) (hRaw : raw < 2 ^ 256)
    (hSeed :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).world.memory
        0x00).val = seed)
    (hCN :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).bindings
        "currentNode" = currentNode)
    (hCsum :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).bindings
        "csum" = csum)
    (hWBase :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).bindings
        "wotsBase" = wotsBase)
    (hWPtr :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).bindings
        "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = j →
        s.world =
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 j).world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep st 0 42).world.memory
      (0x80 + 32 * j)).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
        (wotsBase ||| (j <<< 64))
        ((currentNode >>> (128 + 3 * j)) &&& 7)
        (7 - ((currentNode >>> (128 + 3 * j)) &&& 7)) 0
        (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := by
  exact c12WotsMessageLoop_mem_at_j_eq_of_suffix_preserves
    st j seed currentNode csum wotsBase wotsPtr raw hj hCNLt hWBaseLt hCsumLt hRaw
    hSeed hCN hCsum hWBase hWPtr hCdLoad
    (fun s idx hjidx hidx =>
      c12WotsMessageStep_preserves_prior_message_cell s j idx hjidx hidx)

theorem c12WotsMessageFold_preserves_currentNode
    (st : RuntimeState) (start stop : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop
          "i" c12WotsMessageStep st start stop).bindings
        "currentNode" =
      lookupValue st.bindings "currentNode" := by
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "i" "currentNode" c12WotsMessageStep (by decide)
    (fun s => c12WotsMessageStep_preserves_lookup_of_fresh
      "currentNode" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s)]

theorem c12WotsMessageFold_preserves_wotsBase
    (st : RuntimeState) (start stop : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop
          "i" c12WotsMessageStep st start stop).bindings
        "wotsBase" =
      lookupValue st.bindings "wotsBase" := by
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "i" "wotsBase" c12WotsMessageStep (by decide)
    (fun s => c12WotsMessageStep_preserves_lookup_of_fresh
      "wotsBase" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s)]

theorem c12WotsMessageFold_preserves_wotsPtr
    (st : RuntimeState) (start stop : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop
          "i" c12WotsMessageStep st start stop).bindings
        "wotsPtr" =
      lookupValue st.bindings "wotsPtr" := by
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "i" "wotsPtr" c12WotsMessageStep (by decide)
    (fun s => c12WotsMessageStep_preserves_lookup_of_fresh
      "wotsPtr" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s)]

theorem c12WotsMessageFold_preserves_memory_zero_bound
    (st : RuntimeState) (remaining : Nat) (hrem : remaining ≤ 42) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop
      "i" c12WotsMessageStep st 0 remaining).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  exact SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_memory_val_range
    "i" c12WotsMessageStep 0x00 (fun idx => idx < 42)
    (fun s idx hidx =>
      c12WotsMessageBody_preserves_memory_zero_bound
        s idx hidx
        (c12WotsMessageStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) })
        (execC12WotsMessageBody
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }))
    st 0 remaining
    (fun i _ hi => by omega)

set_option maxHeartbeats 600000 in
/-- One C12 WOTS message-loop step increases the checksum accumulator by at
most seven, for the concrete message-loop index range. -/
theorem c12WotsMessageStep_csum_le_add7
    (st : RuntimeState) (idx csum currentNode : Nat)
    (hidx : idx < 42)
    (hCNLt : currentNode < 2 ^ 256)
    (hCsumLt : csum + 7 < 2 ^ 256)
    (hI : lookupValue st.bindings "i" = idx)
    (hCN : lookupValue st.bindings "currentNode" = currentNode)
    (hCsum : lookupValue st.bindings "csum" = csum) :
    lookupValue (c12WotsMessageStep st).bindings "csum" ≤ csum + 7 := by
  have hILt : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hMulLt : 3 * idx < 2 ^ 256 := by
    have h1 : 3 * idx ≤ 3 * 41 := Nat.mul_le_mul_left _ (by omega)
    have h2 : (3 : Nat) * 41 < 2 ^ 256 := by decide
    omega
  have hShiftLt : 128 + 3 * idx < 2 ^ 256 := by
    have h1 : 128 + 3 * idx ≤ 128 + 3 * 41 := by omega
    have h2 : (128 : Nat) + 3 * 41 < 2 ^ 256 := by decide
    omega
  let digit : Nat := (currentNode >>> (128 + 3 * idx)) &&& 7
  have hDigitLe : digit ≤ 7 := by
    dsimp [digit]
    exact and_seven_le_seven _
  have hCsumLt' : csum < 2 ^ 256 := by omega
  have hSumLt : csum + (7 - digit) < 2 ^ 256 := by
    have hle : 7 - digit ≤ 7 := by omega
    omega
  have hStep1 := execStmt_letVar_digit_eq st idx currentNode hI hCN hILt hCNLt
    hMulLt hShiftLt
  let state1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "digit" digit }
  have hCsum1 : lookupValue state1.bindings "csum" = csum := by
    dsimp [state1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "digit" "csum" _ (by decide)]
    exact hCsum
  have hDigit1 : lookupValue state1.bindings "digit" = digit := by
    dsimp [state1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hStep2 := execStmt_assignVar_csum_eq state1 csum digit hCsum1 hDigit1
    hDigitLe hCsumLt' hSumLt
  let state2 : RuntimeState :=
    { state1 with bindings := bindValue state1.bindings "csum" (csum + (7 - digit)) }
  have hBody := execC12WotsMessageBody st
  rw [c12WotsMessageBody] at hBody
  rw [execStmtList_cons_continue _ _ _ _ hStep1] at hBody
  rw [execStmtList_cons_continue _ _ _ _ hStep2] at hBody
  have hTail :
      lookupValue (c12WotsMessageStep st).bindings "csum" =
        lookupValue state2.bindings "csum" := by
    exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
      "csum"
      [ .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)),
        .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i"))),
        .letVar "steps" (subE (u 7) (v "digit")),
        .forEach "s" (v "steps") c12WotsChainBody,
        mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ]
      state2 (c12WotsMessageStep st)
      (by
        intro s s'' stmt hmem hexec
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            _ _ "val" "csum" _ (by decide) hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            _ _ "chainBase" "csum" _ (by decide) hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            _ _ "steps" "csum" _ (by decide) hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
            "s" "csum" _ _ _ _ (by decide)
            (by
              intro s s'' stmt hmem hexec
              simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                or_false] at hmem
              rcases hmem with rfl | rfl | rfl
              · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                  _ _ "csum" _ _ hexec
              · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                  _ _ "csum" _ _ hexec
              · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                  _ _ "val" "csum" _ (by decide) hexec)
            hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            _ _ "csum" _ _ hexec)
      hBody
  rw [hTail]
  dsimp [state2]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  omega

private theorem c12_nat_land_low3 (x : Nat) : Nat.land x 0x7 = x % 8 := by
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

set_option maxHeartbeats 700000 in
/-- Exact checksum-accumulator update for one C12 WOTS message-loop step. -/
theorem c12WotsMessageStep_csum_eq
    (st : RuntimeState) (idx csum currentNode : Nat)
    (hidx : idx < 42)
    (hCNLt : currentNode < 2 ^ 256)
    (hCsumLt : csum + 7 < 2 ^ 256)
    (hI : lookupValue st.bindings "i" = idx)
    (hCN : lookupValue st.bindings "currentNode" = currentNode)
    (hCsum : lookupValue st.bindings "csum" = csum) :
    lookupValue (c12WotsMessageStep st).bindings "csum" =
      csum + (7 - SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 currentNode idx) := by
  have hILt : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hMulLt : 3 * idx < 2 ^ 256 := by
    have h1 : 3 * idx ≤ 3 * 41 := Nat.mul_le_mul_left _ (by omega)
    have h2 : (3 : Nat) * 41 < 2 ^ 256 := by decide
    omega
  have hShiftLt : 128 + 3 * idx < 2 ^ 256 := by
    have h1 : 128 + 3 * idx ≤ 128 + 3 * 41 := by omega
    have h2 : (128 : Nat) + 3 * 41 < 2 ^ 256 := by decide
    omega
  let digit : Nat := (currentNode >>> (128 + 3 * idx)) &&& 7
  have hDigitLe : digit ≤ 7 := by
    dsimp [digit]
    exact and_seven_le_seven _
  have hDigitSpec :
      digit = SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 currentNode idx := by
    dsimp [digit, SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12]
    change Nat.land (currentNode >>> (128 + 3 * idx)) 7 =
      (currentNode >>> (128 + 3 * idx)) % 8
    exact c12_nat_land_low3 _
  have hCsumLt' : csum < 2 ^ 256 := by omega
  have hSumLt : csum + (7 - digit) < 2 ^ 256 := by
    have hle : 7 - digit ≤ 7 := by omega
    omega
  have hStep1 := execStmt_letVar_digit_eq st idx currentNode hI hCN hILt hCNLt
    hMulLt hShiftLt
  let state1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "digit" digit }
  have hCsum1 : lookupValue state1.bindings "csum" = csum := by
    dsimp [state1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "digit" "csum" _ (by decide)]
    exact hCsum
  have hDigit1 : lookupValue state1.bindings "digit" = digit := by
    dsimp [state1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hStep2 := execStmt_assignVar_csum_eq state1 csum digit hCsum1 hDigit1
    hDigitLe hCsumLt' hSumLt
  let state2 : RuntimeState :=
    { state1 with bindings := bindValue state1.bindings "csum" (csum + (7 - digit)) }
  have hBody := execC12WotsMessageBody st
  rw [c12WotsMessageBody] at hBody
  rw [execStmtList_cons_continue _ _ _ _ hStep1] at hBody
  rw [execStmtList_cons_continue _ _ _ _ hStep2] at hBody
  have hTail :
      lookupValue (c12WotsMessageStep st).bindings "csum" =
        lookupValue state2.bindings "csum" := by
    exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
      "csum"
      [ .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)),
        .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i"))),
        .letVar "steps" (subE (u 7) (v "digit")),
        .forEach "s" (v "steps") c12WotsChainBody,
        mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ]
      state2 (c12WotsMessageStep st)
      (by
        intro s s'' stmt hmem hexec
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            _ _ "val" "csum" _ (by decide) hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            _ _ "chainBase" "csum" _ (by decide) hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            _ _ "steps" "csum" _ (by decide) hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
            "s" "csum" _ _ _ _ (by decide)
            (by
              intro s s'' stmt hmem hexec
              simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                or_false] at hmem
              rcases hmem with rfl | rfl | rfl
              · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                  _ _ "csum" _ _ hexec
              · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                  _ _ "csum" _ _ hexec
              · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                  _ _ "val" "csum" _ (by decide) hexec)
            hexec
        · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            _ _ "csum" _ _ hexec)
      hBody
  rw [hTail]
  dsimp [state2]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  rw [hDigitSpec]

set_option maxHeartbeats 600000 in
/-- Range-indexed checksum bound for the C12 WOTS message fold. -/
theorem c12WotsMessageFold_csum_bound_aux
    (st : RuntimeState) (start remaining currentNode : Nat)
    (hrange : start + remaining ≤ 42)
    (hCNLt : currentNode < 2 ^ 256)
    (hCN : lookupValue st.bindings "currentNode" = currentNode)
    (hCsum : lookupValue st.bindings "csum" ≤ 7 * start) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop
          "i" c12WotsMessageStep st start remaining).bindings
        "csum" ≤ 7 * (start + remaining) := by
  induction remaining generalizing st start with
  | zero =>
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
      simpa using hCsum
  | succ remaining ih =>
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      let sIdx : RuntimeState :=
        { st with bindings := bindValue st.bindings "i" (wordNormalize start) }
      have hstart : start < 42 := by omega
      have hIdxLookup : lookupValue sIdx.bindings "i" = start := by
        dsimp [sIdx]
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
          c12_wots_idxNorm67 start (by omega)]
      have hCurIdx : lookupValue sIdx.bindings "currentNode" = currentNode := by
        dsimp [sIdx]
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
          _ "i" "currentNode" _ (by decide)]
        exact hCN
      have hCsumIdxLe : lookupValue sIdx.bindings "csum" ≤ 7 * start := by
        dsimp [sIdx]
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
          _ "i" "csum" _ (by decide)]
        exact hCsum
      let csumNow := lookupValue sIdx.bindings "csum"
      have hCsumNowLt : csumNow + 7 < 2 ^ 256 := by
        dsimp [csumNow] at *
        have hsmall : 7 * start + 7 ≤ 7 * 42 := by nlinarith
        have hmod : (7 : Nat) * 42 < 2 ^ 256 := by decide
        omega
      have hStepBound :=
        c12WotsMessageStep_csum_le_add7 sIdx start csumNow currentNode hstart hCNLt
          hCsumNowLt hIdxLookup hCurIdx rfl
      have hStepCsum :
          lookupValue (c12WotsMessageStep sIdx).bindings "csum" ≤ 7 * (start + 1) := by
        dsimp [csumNow] at hStepBound
        nlinarith
      have hStepCN :
          lookupValue (c12WotsMessageStep sIdx).bindings "currentNode" = currentNode := by
        rw [c12WotsMessageStep_preserves_lookup_of_fresh
          "currentNode" (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) sIdx]
        exact hCurIdx
      have hRec := ih (c12WotsMessageStep sIdx) (start + 1) (by omega)
        hStepCN hStepCsum
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRec

/-- The first `j` C12 WOTS message iterations keep the checksum accumulator
bounded by `7*j`, starting from zero. -/
theorem c12WotsMessageFold_csum_bound
    (st : RuntimeState) (j currentNode : Nat)
    (hj : j ≤ 42)
    (hCNLt : currentNode < 2 ^ 256)
    (hCN : lookupValue st.bindings "currentNode" = currentNode)
    (hCsum0 : lookupValue st.bindings "csum" = 0) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop
          "i" c12WotsMessageStep st 0 j).bindings
        "csum" ≤ 7 * j := by
  simpa using
    c12WotsMessageFold_csum_bound_aux st 0 j currentNode (by simpa using hj)
      hCNLt hCN (by omega)

private theorem c12WotsCsum_range'_step
    (node acc start remaining : Nat) :
    SphincsMinusVerifiers.ClimbLoop.specFold
        (fun idx acc => acc + (7 - SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 node idx))
        acc start remaining =
      (List.range' start remaining).foldl
        (fun acc idx => acc + (7 - SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 node idx)) acc := by
  induction remaining generalizing acc start with
  | zero =>
      rw [SphincsMinusVerifiers.ClimbLoop.specFold_zero, List.range'_zero]
      rfl
  | succ remaining ih =>
      rw [SphincsMinusVerifiers.ClimbLoop.specFold_succ, List.range'_succ]
      exact ih
        (acc + (7 - SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 node start))
        (start + 1)

set_option maxHeartbeats 700000 in
/-- Exact checksum accumulator after a C12 WOTS message-loop prefix. -/
theorem c12WotsMessageFold_csum_eq_range'
    (st : RuntimeState) (start remaining currentNode csum : Nat)
    (hrange : start + remaining ≤ 42)
    (hCNLt : currentNode < 2 ^ 256)
    (hCN : lookupValue st.bindings "currentNode" = currentNode)
    (hCsum : lookupValue st.bindings "csum" = csum)
    (hCsumLe : csum ≤ 7 * start) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop
          "i" c12WotsMessageStep st start remaining).bindings
        "csum" =
      (List.range' start remaining).foldl
        (fun acc idx =>
          acc + (7 - SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 currentNode idx)) csum := by
  induction remaining generalizing st start csum with
  | zero =>
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero, List.range'_zero]
      simpa using hCsum
  | succ remaining ih =>
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      let sIdx : RuntimeState :=
        { st with bindings := bindValue st.bindings "i" (wordNormalize start) }
      have hstart : start < 42 := by omega
      have hIdxLookup : lookupValue sIdx.bindings "i" = start := by
        dsimp [sIdx]
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
          c12_wots_idxNorm67 start (by omega)]
      have hCurIdx : lookupValue sIdx.bindings "currentNode" = currentNode := by
        dsimp [sIdx]
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
          _ "i" "currentNode" _ (by decide)]
        exact hCN
      have hCsumIdx : lookupValue sIdx.bindings "csum" = csum := by
        dsimp [sIdx]
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
          _ "i" "csum" _ (by decide)]
        exact hCsum
      have hCsumLt : csum + 7 < 2 ^ 256 := by
        have hsmall : 7 * start + 7 ≤ 7 * 42 := by nlinarith
        have hmod : (7 : Nat) * 42 < 2 ^ 256 := by decide
        omega
      have hStep :=
        c12WotsMessageStep_csum_eq sIdx start csum currentNode hstart hCNLt
          hCsumLt hIdxLookup hCurIdx hCsumIdx
      let csumNext :=
        csum + (7 - SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 currentNode start)
      have hStepCN :
          lookupValue (c12WotsMessageStep sIdx).bindings "currentNode" = currentNode := by
        rw [c12WotsMessageStep_preserves_lookup_of_fresh
          "currentNode" (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) sIdx]
        exact hCurIdx
      have hNextLe : csumNext ≤ 7 * (start + 1) := by
        dsimp [csumNext]
        have hDigitLe :
            SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 currentNode start ≤ 7 := by
          unfold SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12
          have hlt := Nat.mod_lt (currentNode >>> (128 + 3 * start))
            (by decide : 0 < 8)
          omega
        have hSubLe :
            7 - SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 currentNode start ≤ 7 :=
          Nat.sub_le _ _
        calc
          csum + (7 - SphincsMinusVerifierSpec.C12Concrete.wotsDigitC12 currentNode start)
              ≤ csum + 7 := Nat.add_le_add_left hSubLe csum
          _ ≤ 7 * start + 7 := Nat.add_le_add_right hCsumLe 7
          _ = 7 * (start + 1) := by ring
      have hRec :=
        ih (c12WotsMessageStep sIdx) (start + 1) csumNext (by omega)
          hStepCN (by simpa [csumNext] using hStep) hNextLe
      rw [List.range'_succ]
      simp only [List.foldl_cons]
      simpa [sIdx, csumNext] using hRec

/-- Exact final checksum accumulator after the 42 C12 WOTS message iterations. -/
theorem c12WotsMessageFold_csum_eq_wotsCsum
    (st : RuntimeState) (currentNode : Nat)
    (hCNLt : currentNode < 2 ^ 256)
    (hCN : lookupValue st.bindings "currentNode" = currentNode)
    (hCsum0 : lookupValue st.bindings "csum" = 0) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop
          "i" c12WotsMessageStep st 0 42).bindings
        "csum" =
      SphincsMinusVerifierSpec.C12Concrete.wotsCsumC12 currentNode := by
  have h :=
    c12WotsMessageFold_csum_eq_range' st 0 42 currentNode 0
      (by omega) hCNLt hCN hCsum0 (by omega)
  simpa [SphincsMinusVerifierSpec.C12Concrete.wotsCsumC12] using h

set_option maxHeartbeats 1000000 in
theorem c12WotsChecksumBody_preserves_memory_zero_bound
    (s : RuntimeState) (idx : Nat) (hidx : idx < 3) (s'' : RuntimeState)
    (hExec : execStmtList []
      { s with bindings := bindValue s.bindings "j" (wordNormalize idx) }
      c12WotsChecksumBody = .continue s'') :
    (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "j" (wordNormalize idx) }
  rw [c12WotsChecksumBody_eq_prefix_tail, MemoryKit.execStmtList_append] at hExec
  cases hp : execStmtList [] st c12WotsChecksumPrefix with
  | «continue» mid =>
      rw [hp] at hExec
      have hprefixMem := c12WotsChecksumPrefix_preserves_memory_zero st mid hp
      have hjSt : lookupValue st.bindings "j" = idx := by
        dsimp [st]
        rw [MemoryKit.lookupValue_bindValue_self]
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (lt_trans hidx (by decide))]
      obtain ⟨vdigit, hdigitEval⟩ : ∃ val, evalExpr [] st
          (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)) =
            some val := ⟨_, rfl⟩
      have hdigitStmt := MemoryKit.execStmt_letVar_continue st "digit" _ vdigit hdigitEval
      let stD : RuntimeState := { st with bindings := bindValue st.bindings "digit" vdigit }
      have hjD : lookupValue stD.bindings "j" = idx := by
        dsimp [stD]
        rw [MemoryKit.lookupValue_bindValue_ne _ "digit" "j" _ (by decide), hjSt]
      have hjEval : evalExpr [] stD (v "j") = some idx := by
        show some (lookupValue stD.bindings "j") = some idx
        rw [hjD]
      have h42 : evalExpr [] stD (u 42) = some 42 := by rfl
      have hiEval : evalExpr [] stD (addE (u 42) (v "j")) = some (42 + idx) := by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
          stD (u 42) (v "j") 42 idx h42 hjEval
          (by decide) (lt_trans hidx (by decide)) (by omega)
      have hiStmt := MemoryKit.execStmt_letVar_continue stD "i" _ (42 + idx) hiEval
      let stI : RuntimeState := { stD with bindings := bindValue stD.bindings "i" (42 + idx) }
      have hsplit : c12WotsChecksumPrefix =
          [ .letVar "digit" (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7))
          , .letVar "i" (addE (u 42) (v "j")) ] ++
          [ .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
          , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
          , .letVar "steps" (subE (u 7) (v "digit"))
          , .forEach "s" (v "steps") c12WotsChainBody ] := rfl
      have hpTail : execStmtList [] stI
          [ .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
          , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
          , .letVar "steps" (subE (u 7) (v "digit"))
          , .forEach "s" (v "steps") c12WotsChainBody ] = .continue mid := by
        rw [hsplit, MemoryKit.execStmtList_append] at hp
        rw [execStmtList_cons_continue _ _ _ _ hdigitStmt] at hp
        rw [show { st with bindings := bindValue st.bindings "digit" vdigit } = stD from rfl] at hp
        rw [execStmtList_cons_continue _ _ _ _ hiStmt] at hp
        exact hp
      have htailI := c12WotsChecksumTail_preserves_i stI mid hpTail
      have hstII : lookupValue stI.bindings "i" = 42 + idx := by
        dsimp [stI]
        exact MemoryKit.lookupValue_bindValue_self stD.bindings "i" (42 + idx)
      have hmidI : lookupValue mid.bindings "i" = 42 + idx := by
        rw [htailI, hstII]
      have hoff : evalExpr [] mid (addE (u 0x80) (shlE (u 5) (v "i"))) =
          some (0x80 + 32 * (42 + idx)) :=
        evalC12WotsOffset_of_lookup mid 0x80 (42 + idx) (by decide) (by omega) hmidI
      have hval : evalExpr [] mid (v "val") = some (lookupValue mid.bindings "val") := rfl
      let out : RuntimeState :=
        { mid with world := { mid.world with
            memory := MemoryKit.memUpdate mid.world.memory (0x80 + 32 * (42 + idx))
              (lookupValue mid.bindings "val") } }
      have hstore : execStmt [] mid
          (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) =
          .continue out := by
        unfold out mstoreE
        exact execStmt_mstore_continue mid
          (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
          (0x80 + 32 * (42 + idx)) (lookupValue mid.bindings "val") hoff hval
      change (match execStmt [] mid
          (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) with
        | .continue n => execStmtList [] n []
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) = .continue s'' at hExec
      rw [hstore] at hExec
      simp only [execStmtList] at hExec
      injection hExec with hs
      subst s''
      unfold out
      change (MemoryKit.memUpdate mid.world.memory (0x80 + 32 * (42 + idx))
          (lookupValue mid.bindings "val") 0x00).val =
        (s.world.memory 0x00).val
      rw [MemoryKit.memUpdate_diff _ (0x80 + 32 * (42 + idx)) 0x00
        (lookupValue mid.bindings "val") (by omega)]
      exact hprefixMem
  | stop stopped => rw [hp] at hExec; simp at hExec
  | «return» rv rst => rw [hp] at hExec; simp at hExec
  | revert => rw [hp] at hExec; simp at hExec

set_option maxHeartbeats 1000000 in
theorem c12WotsChecksumBody_preserves_memory_addr_of_ne_bound
    (s : RuntimeState) (idx addr : Nat) (hidx : idx < 3)
    (h20 : addr ≠ 0x20) (h40 : addr ≠ 0x40)
    (hFinal : addr ≠ 0x80 + 32 * (42 + idx)) (s'' : RuntimeState)
    (hExec : execStmtList []
      { s with bindings := bindValue s.bindings "j" (wordNormalize idx) }
      c12WotsChecksumBody = .continue s'') :
    (s''.world.memory addr).val = (s.world.memory addr).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "j" (wordNormalize idx) }
  rw [c12WotsChecksumBody_eq_prefix_tail, MemoryKit.execStmtList_append] at hExec
  cases hp : execStmtList [] st c12WotsChecksumPrefix with
  | «continue» mid =>
      rw [hp] at hExec
      have hprefixMem :=
        c12WotsChecksumPrefix_preserves_memory_addr_of_ne addr h20 h40 st mid hp
      have hjSt : lookupValue st.bindings "j" = idx := by
        dsimp [st]
        rw [MemoryKit.lookupValue_bindValue_self]
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (lt_trans hidx (by decide))]
      obtain ⟨vdigit, hdigitEval⟩ : ∃ val, evalExpr [] st
          (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)) =
            some val := ⟨_, rfl⟩
      have hdigitStmt := MemoryKit.execStmt_letVar_continue st "digit" _ vdigit hdigitEval
      let stD : RuntimeState := { st with bindings := bindValue st.bindings "digit" vdigit }
      have hjD : lookupValue stD.bindings "j" = idx := by
        dsimp [stD]
        rw [MemoryKit.lookupValue_bindValue_ne _ "digit" "j" _ (by decide), hjSt]
      have hjEval : evalExpr [] stD (v "j") = some idx := by
        show some (lookupValue stD.bindings "j") = some idx
        rw [hjD]
      have h42 : evalExpr [] stD (u 42) = some 42 := by rfl
      have hiEval : evalExpr [] stD (addE (u 42) (v "j")) = some (42 + idx) := by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
          stD (u 42) (v "j") 42 idx h42 hjEval
          (by decide) (lt_trans hidx (by decide)) (by omega)
      have hiStmt := MemoryKit.execStmt_letVar_continue stD "i" _ (42 + idx) hiEval
      let stI : RuntimeState := { stD with bindings := bindValue stD.bindings "i" (42 + idx) }
      have hsplit : c12WotsChecksumPrefix =
          [ .letVar "digit" (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7))
          , .letVar "i" (addE (u 42) (v "j")) ] ++
          [ .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
          , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
          , .letVar "steps" (subE (u 7) (v "digit"))
          , .forEach "s" (v "steps") c12WotsChainBody ] := rfl
      have hpTail : execStmtList [] stI
          [ .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
          , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
          , .letVar "steps" (subE (u 7) (v "digit"))
          , .forEach "s" (v "steps") c12WotsChainBody ] = .continue mid := by
        rw [hsplit, MemoryKit.execStmtList_append] at hp
        rw [execStmtList_cons_continue _ _ _ _ hdigitStmt] at hp
        rw [show { st with bindings := bindValue st.bindings "digit" vdigit } = stD from rfl] at hp
        rw [execStmtList_cons_continue _ _ _ _ hiStmt] at hp
        exact hp
      have htailI := c12WotsChecksumTail_preserves_i stI mid hpTail
      have hstII : lookupValue stI.bindings "i" = 42 + idx := by
        dsimp [stI]
        exact MemoryKit.lookupValue_bindValue_self stD.bindings "i" (42 + idx)
      have hmidI : lookupValue mid.bindings "i" = 42 + idx := by
        rw [htailI, hstII]
      have hoff : evalExpr [] mid (addE (u 0x80) (shlE (u 5) (v "i"))) =
          some (0x80 + 32 * (42 + idx)) :=
        evalC12WotsOffset_of_lookup mid 0x80 (42 + idx) (by decide) (by omega) hmidI
      have hval : evalExpr [] mid (v "val") = some (lookupValue mid.bindings "val") := rfl
      let out : RuntimeState :=
        { mid with world := { mid.world with
            memory := MemoryKit.memUpdate mid.world.memory (0x80 + 32 * (42 + idx))
              (lookupValue mid.bindings "val") } }
      have hstore : execStmt [] mid
          (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) =
          .continue out := by
        unfold out mstoreE
        exact execStmt_mstore_continue mid
          (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
          (0x80 + 32 * (42 + idx)) (lookupValue mid.bindings "val") hoff hval
      change (match execStmt [] mid
          (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) with
        | .continue n => execStmtList [] n []
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) = .continue s'' at hExec
      rw [hstore] at hExec
      simp only [execStmtList] at hExec
      injection hExec with hs
      subst s''
      unfold out
      change (MemoryKit.memUpdate mid.world.memory (0x80 + 32 * (42 + idx))
          (lookupValue mid.bindings "val") addr).val =
        (s.world.memory addr).val
      rw [MemoryKit.memUpdate_diff _ (0x80 + 32 * (42 + idx)) addr
        (lookupValue mid.bindings "val") hFinal]
      exact hprefixMem
  | stop stopped => rw [hp] at hExec; simp at hExec
  | «return» rv rst => rw [hp] at hExec; simp at hExec
  | revert => rw [hp] at hExec; simp at hExec

/-- A later C12 WOTS checksum-loop iteration preserves an earlier checksum cell. -/
theorem c12WotsChecksumStep_preserves_prior_checksum_cell
    (s : RuntimeState) (j idx : Nat) (hjidx : j < idx) (hidx : idx < 3) :
    ((c12WotsChecksumStep
      { s with bindings := bindValue s.bindings "j" (wordNormalize idx) }).world.memory
      (0x80 + 32 * (42 + j))).val =
      (s.world.memory (0x80 + 32 * (42 + j))).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "j" (wordNormalize idx) }
  exact c12WotsChecksumBody_preserves_memory_addr_of_ne_bound
    s idx (0x80 + 32 * (42 + j)) hidx (by omega) (by omega) (by omega)
    (c12WotsChecksumStep st) (execC12WotsChecksumBody st)

/-- The C12 WOTS checksum loop writes only the final three chain cells, so it
preserves every earlier message-loop cell. -/
theorem c12WotsChecksumLoop_preserves_message_cell
    (s : RuntimeState) (j : Nat) (hj : j < 42) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep s 0 3).world.memory
      (0x80 + 32 * j)).val =
      (s.world.memory (0x80 + 32 * j)).val :=
  SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_memory_val_range
    "j" c12WotsChecksumStep (0x80 + 32 * j) (fun idx => idx < 3)
    (fun s idx hidx =>
      c12WotsChecksumBody_preserves_memory_addr_of_ne_bound
        s idx (0x80 + 32 * j) hidx (by omega) (by omega) (by omega)
        (c12WotsChecksumStep
          { s with bindings := bindValue s.bindings "j" (wordNormalize idx) })
        (execC12WotsChecksumBody
          { s with bindings := bindValue s.bindings "j" (wordNormalize idx) }))
    s 0 3
    (fun i _ hi => by omega)

/-- The bounded checksum loop preserves the public-seed scratch cell. -/
theorem c12WotsChecksumFold_preserves_memory_zero_bound
    (s : RuntimeState) (j : Nat) (hj : j ≤ 3) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep s 0 j).world.memory
      0x00).val =
      (s.world.memory 0x00).val :=
  SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_memory_val_range
    "j" c12WotsChecksumStep 0x00 (fun idx => idx < 3)
    (fun s idx hidx =>
      c12WotsChecksumBody_preserves_memory_zero_bound
        s idx hidx
        (c12WotsChecksumStep
          { s with bindings := bindValue s.bindings "j" (wordNormalize idx) })
        (execC12WotsChecksumBody
          { s with bindings := bindValue s.bindings "j" (wordNormalize idx) }))
    s 0 j
    (fun i _ hi => by omega)

set_option maxHeartbeats 1000000 in
/-- One full C12 WOTS checksum-step iteration writes the expected chain hash
into checksum cell `0x80 + 32 * (42 + j)`.

The checksum digit evaluation and calldata correspondence are explicit
hypotheses, matching the message-loop theorem style while avoiding a larger
checksum-prefix evaluator in this bounded step. -/
theorem c12WotsChecksumStep_mem_at_j_eq
    (st : RuntimeState) (j seed digit wotsBase wotsPtr raw : Nat)
    (hj : j < 3)
    (hWBaseLt : wotsBase < 2 ^ 256) (hDigitLe : digit ≤ 7)
    (hRaw : raw < 2 ^ 256)
    (hSeed : (st.world.memory 0x00).val = seed)
    (hJ : lookupValue st.bindings "j" = j)
    (hWBase : lookupValue st.bindings "wotsBase" = wotsBase)
    (hWPtr : lookupValue st.bindings "wotsPtr" = wotsPtr)
    (hDigitEval : evalExpr [] st
        (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)) =
      some digit)
    (hCdLoad : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = 42 + j →
        s.world = st.world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw) :
    ((c12WotsChecksumStep st).world.memory (0x80 + 32 * (42 + j))).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
        (wotsBase ||| ((42 + j) <<< 64)) digit (7 - digit) 0
        (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := by
  have hILt : 42 + j < 2 ^ 256 := by omega
  have hShlLt : (42 + j) <<< 64 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have h1 : (42 + j) * 2 ^ 64 ≤ 44 * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (44 : Nat) * 2 ^ 64 < 2 ^ 256 := by decide
    omega
  have hChainBaseLt : wotsBase ||| ((42 + j) <<< 64) < 2 ^ 256 := by
    show Nat.bitwise or wotsBase ((42 + j) <<< 64) < 2 ^ 256
    exact Nat.bitwise_lt_two_pow hWBaseLt hShlLt
  have hVal0Lt : SphincsMinusVerifierSpec.C13Concrete.maskN raw < 2 ^ 256 := by
    show Nat.bitwise and raw SphincsMinusVerifierSpec.C13Concrete.nMask < 2 ^ 256
    exact Nat.bitwise_lt_two_pow hRaw
      SphincsMinusVerifiers.ClimbKeccakStep.nMask_lt
  -- Step 1: letVar "digit"
  have hStep1 := SphincsMinusVerifiers.MemoryKit.execStmt_letVar_continue st
    "digit"
    (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7))
    digit hDigitEval
  let state1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "digit" digit }
  have hJ1 : lookupValue state1.bindings "j" = j := by
    dsimp [state1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "digit" "j" _ (by decide)]
    exact hJ
  have hJEval1 : evalExpr [] state1 (v "j") = some j := by
    show some (lookupValue state1.bindings "j") = some j
    rw [hJ1]
  have h42 : evalExpr [] state1 (u 42) = some 42 := by rfl
  -- Step 2: letVar "i"
  have hIEval : evalExpr [] state1 (addE (u 42) (v "j")) = some (42 + j) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      state1 (u 42) (v "j") 42 j h42 hJEval1
      (by decide) (lt_trans hj (by decide)) hILt
  have hStep2 := SphincsMinusVerifiers.MemoryKit.execStmt_letVar_continue state1
    "i" (addE (u 42) (v "j")) (42 + j) hIEval
  let state2 : RuntimeState :=
    { state1 with bindings := bindValue state1.bindings "i" (42 + j) }
  have hWPtr2 : lookupValue state2.bindings "wotsPtr" = wotsPtr := by
    dsimp [state2, state1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "wotsPtr" _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "digit" "wotsPtr" _ (by decide)]
    exact hWPtr
  have hI2 : lookupValue state2.bindings "i" = 42 + j := by
    dsimp [state2]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hCdLoad2 := hCdLoad state2 hWPtr2 hI2 rfl
  -- Step 3: letVar "val"
  have hStep3 := execStmt_letVar_val_eq state2 raw hCdLoad2 hRaw
  let state3 : RuntimeState :=
    { state2 with bindings := bindValue state2.bindings "val" (SphincsMinusVerifierSpec.C13Concrete.maskN raw) }
  have hWBase3 : lookupValue state3.bindings "wotsBase" = wotsBase := by
    dsimp [state3, state2, state1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "val" "wotsBase" _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "wotsBase" _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "digit" "wotsBase" _ (by decide)]
    exact hWBase
  have hI3 : lookupValue state3.bindings "i" = 42 + j := by
    dsimp [state3]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "val" "i" _ (by decide)]
    exact hI2
  -- Step 4: letVar "chainBase"
  have hStep4 := execStmt_letVar_chainBase_eq state3 wotsBase (42 + j)
    hWBase3 hI3 hWBaseLt hILt hShlLt
  let state4 : RuntimeState :=
    { state3 with bindings :=
        (bindValue state3.bindings "chainBase" (wotsBase ||| ((42 + j) <<< 64))) }
  have hDigit4 : lookupValue state4.bindings "digit" = digit := by
    dsimp [state4, state3, state2, state1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "chainBase" "digit" _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "val" "digit" _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "digit" _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  -- Step 5: letVar "steps"
  have hStep5 := execStmt_letVar_steps_eq state4 digit hDigit4 hDigitLe
  let state5 : RuntimeState :=
    { state4 with bindings := bindValue state4.bindings "steps" (7 - digit) }
  have hPrefix5 : execStmtList [] st
      [ .letVar "digit"
          (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7))
      , .letVar "i" (addE (u 42) (v "j"))
      , .letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
      , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
      , .letVar "steps" (subE (u 7) (v "digit"))
      ] = .continue state5 := by
    rw [execStmtList_cons_continue _ _ _ _ hStep1]
    rw [show { st with bindings := bindValue st.bindings "digit" digit } = state1 from rfl]
    rw [execStmtList_cons_continue _ _ _ _ hStep2]
    rw [show { state1 with bindings := bindValue state1.bindings "i" (42 + j) } =
      state2 from rfl]
    rw [execStmtList_cons_continue _ _ _ _ hStep3]
    rw [show { state2 with bindings := bindValue state2.bindings "val" (SphincsMinusVerifierSpec.C13Concrete.maskN raw) } = state3 from rfl]
    rw [execStmtList_cons_continue _ _ _ _ hStep4]
    rw [show { state3 with bindings :=
          (bindValue state3.bindings "chainBase" (wotsBase ||| ((42 + j) <<< 64))) } =
      state4 from rfl]
    rw [execStmtList_cons_continue _ _ _ _ hStep5]
    rfl
  have hMem5 : (state5.world.memory 0x00).val = seed := hSeed
  have hI5 : lookupValue state5.bindings "i" = 42 + j := by
    dsimp [state5]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "steps" "i" _ (by decide)]
    dsimp [state4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "chainBase" "i" _ (by decide)]
    exact hI3
  have hCB5 : lookupValue state5.bindings "chainBase" =
      wotsBase ||| ((42 + j) <<< 64) := by
    dsimp [state5, state4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "steps" "chainBase" _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hDigit5 : lookupValue state5.bindings "digit" = digit := by
    dsimp [state5]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "steps" "digit" _ (by decide)]
    exact hDigit4
  have hSteps5 : lookupValue state5.bindings "steps" = 7 - digit := by
    dsimp [state5]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hVal5 : lookupValue state5.bindings "val" =
      SphincsMinusVerifierSpec.C13Concrete.maskN raw := by
    dsimp [state5, state4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "steps" "val" _ (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "chainBase" "val" _ (by decide)]
    dsimp [state3]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  obtain ⟨sFinal, hExecTail, hMemFinal⟩ :=
    c12WotsMessage_chainTail_mem_at_i state5 (42 + j) seed
      (wotsBase ||| ((42 + j) <<< 64)) digit
      (SphincsMinusVerifierSpec.C13Concrete.maskN raw) (by omega)
      hChainBaseLt hDigitLe hVal0Lt hMem5 hI5 hCB5 hDigit5 hSteps5 hVal5
  have hBody : c12WotsChecksumBody =
      [ .letVar "digit"
          (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7))
      , .letVar "i" (addE (u 42) (v "j"))
      , .letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
      , .letVar "chainBase" (orE (v "wotsBase") (shlE (u 64) (v "i")))
      , .letVar "steps" (subE (u 7) (v "digit")) ] ++
      [ .forEach "s" (v "steps") c12WotsChainBody
      , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ] := rfl
  have hExecBody : execStmtList [] st c12WotsChecksumBody = .continue sFinal := by
    rw [hBody,
      SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue _ _ _ _ hPrefix5]
    exact hExecTail
  unfold c12WotsChecksumStep
  rw [hExecBody]
  exact hMemFinal

set_option maxHeartbeats 600000 in
/-- Concrete fixed-cell invariant for the 3-step C12 WOTS checksum loop. -/
theorem c12WotsChecksumLoop_mem_at_j_eq
    (st : RuntimeState) (j seed digit wotsBase wotsPtr raw : Nat)
    (hj : j < 3)
    (hWBaseLt : wotsBase < 2 ^ 256) (hDigitLe : digit ≤ 7)
    (hRaw : raw < 2 ^ 256)
    (hSeed :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).world.memory
        0x00).val = seed)
    (hWBase :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).bindings
        "wotsBase" = wotsBase)
    (hWPtr :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).bindings
        "wotsPtr" = wotsPtr)
    (hDigitEval : ∀ (s : RuntimeState),
        lookupValue s.bindings "j" = j →
        s.world =
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).world →
        evalExpr [] s
          (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)) =
          some digit)
    (hCdLoad : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = 42 + j →
        s.world =
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 3).world.memory
      (0x80 + 32 * (42 + j))).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
        (wotsBase ||| ((42 + j) <<< 64)) digit (7 - digit) 0
        (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := by
  let beforeJ : RuntimeState :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j
  let atJ : RuntimeState :=
    { beforeJ with bindings := bindValue beforeJ.bindings "j" (wordNormalize j) }
  have hStepAt :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_memory_val_eq_step_at_of_suffix_preserves
      "j" c12WotsChecksumStep (0x80 + 32 * (42 + j)) st 0 3 j hj
      (fun s idx hgt hlt =>
        c12WotsChecksumStep_preserves_prior_checksum_cell s j idx (by omega) (by omega))
  have hJAt : lookupValue atJ.bindings "j" = j := by
    dsimp [atJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
      c12_wots_idxNorm67 j (by omega)]
  have hWBaseAt : lookupValue atJ.bindings "wotsBase" = wotsBase := by
    dsimp [atJ, beforeJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "j" "wotsBase" _ (by decide)]
    exact hWBase
  have hWPtrAt : lookupValue atJ.bindings "wotsPtr" = wotsPtr := by
    dsimp [atJ, beforeJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "j" "wotsPtr" _ (by decide)]
    exact hWPtr
  have hSeedAt : (atJ.world.memory 0x00).val = seed := by
    dsimp [atJ, beforeJ]
    exact hSeed
  have hDigitEvalAt : evalExpr [] atJ
        (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)) =
      some digit :=
    hDigitEval atJ hJAt (by simp [atJ, beforeJ])
  have hCdLoadAt : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = 42 + j →
        s.world = atJ.world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw := by
    intro s hw hi hworld
    exact hCdLoad s hw hi (by simpa [atJ, beforeJ] using hworld)
  have hStepMem :
      ((c12WotsChecksumStep atJ).world.memory (0x80 + 32 * (42 + j))).val =
        SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
          (wotsBase ||| ((42 + j) <<< 64)) digit (7 - digit) 0
          (SphincsMinusVerifierSpec.C13Concrete.maskN raw) :=
    c12WotsChecksumStep_mem_at_j_eq atJ j seed digit wotsBase wotsPtr raw hj
      hWBaseLt hDigitLe hRaw hSeedAt hJAt hWBaseAt hWPtrAt hDigitEvalAt hCdLoadAt
  calc
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 3).world.memory
        (0x80 + 32 * (42 + j))).val
        = ((c12WotsChecksumStep
            { (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j) with
              bindings :=
                bindValue
                  (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).bindings
                  "j" (wordNormalize (0 + j)) }).world.memory
            (0x80 + 32 * (42 + j))).val := hStepAt
    _ = ((c12WotsChecksumStep atJ).world.memory (0x80 + 32 * (42 + j))).val := by
      simp [atJ, beforeJ]
    _ = SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
          (wotsBase ||| ((42 + j) <<< 64)) digit (7 - digit) 0
          (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := hStepMem

set_option maxHeartbeats 600000 in
/-- Concrete fixed-cell invariant for the 3-step C12 WOTS checksum loop, with
the checksum digit evaluated only at the actual iteration state.  This is the
usable bridge form for callers that know `"csumShifted"` only on the executable
loop prefix. -/
theorem c12WotsChecksumLoop_mem_at_j_eq_at
    (st : RuntimeState) (j seed digit wotsBase wotsPtr raw : Nat)
    (hj : j < 3)
    (hWBaseLt : wotsBase < 2 ^ 256) (hDigitLe : digit ≤ 7)
    (hRaw : raw < 2 ^ 256)
    (hSeed :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).world.memory
        0x00).val = seed)
    (hWBase :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).bindings
        "wotsBase" = wotsBase)
    (hWPtr :
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).bindings
        "wotsPtr" = wotsPtr)
    (hDigitEval :
      evalExpr []
        { (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j) with
          bindings :=
            bindValue
              (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).bindings
              "j" (wordNormalize j) }
        (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)) =
        some digit)
    (hCdLoad : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = 42 + j →
        s.world =
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 3).world.memory
      (0x80 + 32 * (42 + j))).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
        (wotsBase ||| ((42 + j) <<< 64)) digit (7 - digit) 0
        (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := by
  let beforeJ : RuntimeState :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j
  let atJ : RuntimeState :=
    { beforeJ with bindings := bindValue beforeJ.bindings "j" (wordNormalize j) }
  have hStepAt :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_memory_val_eq_step_at_of_suffix_preserves
      "j" c12WotsChecksumStep (0x80 + 32 * (42 + j)) st 0 3 j hj
      (fun s idx hgt hlt =>
        c12WotsChecksumStep_preserves_prior_checksum_cell s j idx (by omega) (by omega))
  have hJAt : lookupValue atJ.bindings "j" = j := by
    dsimp [atJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
      c12_wots_idxNorm67 j (by omega)]
  have hWBaseAt : lookupValue atJ.bindings "wotsBase" = wotsBase := by
    dsimp [atJ, beforeJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "j" "wotsBase" _ (by decide)]
    exact hWBase
  have hWPtrAt : lookupValue atJ.bindings "wotsPtr" = wotsPtr := by
    dsimp [atJ, beforeJ]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "j" "wotsPtr" _ (by decide)]
    exact hWPtr
  have hSeedAt : (atJ.world.memory 0x00).val = seed := by
    dsimp [atJ, beforeJ]
    exact hSeed
  have hDigitEvalAt : evalExpr [] atJ
        (andE (shrE (subE (u 13) (mulE (u 3) (v "j"))) (v "csumShifted")) (u 7)) =
      some digit := by
    simpa [atJ, beforeJ] using hDigitEval
  have hCdLoadAt : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = 42 + j →
        s.world = atJ.world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw := by
    intro s hw hi hworld
    exact hCdLoad s hw hi (by simpa [atJ, beforeJ] using hworld)
  have hStepMem :
      ((c12WotsChecksumStep atJ).world.memory (0x80 + 32 * (42 + j))).val =
        SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
          (wotsBase ||| ((42 + j) <<< 64)) digit (7 - digit) 0
          (SphincsMinusVerifierSpec.C13Concrete.maskN raw) :=
    c12WotsChecksumStep_mem_at_j_eq atJ j seed digit wotsBase wotsPtr raw hj
      hWBaseLt hDigitLe hRaw hSeedAt hJAt hWBaseAt hWPtrAt hDigitEvalAt hCdLoadAt
  calc
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 3).world.memory
        (0x80 + 32 * (42 + j))).val
        = ((c12WotsChecksumStep
            { (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j) with
              bindings :=
                bindValue
                  (SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep st 0 j).bindings
                  "j" (wordNormalize (0 + j)) }).world.memory
            (0x80 + 32 * (42 + j))).val := hStepAt
    _ = ((c12WotsChecksumStep atJ).world.memory (0x80 + 32 * (42 + j))).val := by
      simp [atJ, beforeJ]
    _ = SphincsMinusVerifierSpec.C12Concrete.chainHashC12 seed
          (wotsBase ||| ((42 + j) <<< 64)) digit (7 - digit) 0
          (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := hStepMem

theorem c12WotsChecksumFold_preserves_wotsBase
    (st : RuntimeState) (start stop : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop
          "j" c12WotsChecksumStep st start stop).bindings
        "wotsBase" =
      lookupValue st.bindings "wotsBase" := by
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "j" "wotsBase" c12WotsChecksumStep (by decide)
    (fun s => c12WotsChecksumStep_preserves_lookup_of_fresh
      "wotsBase" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s)]

theorem c12WotsChecksumFold_preserves_wotsPtr
    (st : RuntimeState) (start stop : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop
          "j" c12WotsChecksumStep st start stop).bindings
        "wotsPtr" =
      lookupValue st.bindings "wotsPtr" := by
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "j" "wotsPtr" c12WotsChecksumStep (by decide)
    (fun s => c12WotsChecksumStep_preserves_lookup_of_fresh
      "wotsPtr" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s)]

/-- A bounded WOTS-PK copy-loop iteration preserves the public-seed scratch cell. -/
theorem c12WotsPkCopyStep_preserves_memory_zero_bound
    (s : RuntimeState) (idx : Nat) (hidx : idx < 67) :
    ((c12WotsPkCopyStep
      { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
      0x00).val =
      (s.world.memory 0x00).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
      some (0x40 + 32 * idx) :=
    evalC12WotsOffset s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) =
      some (0x80 + 32 * idx) :=
    evalC12WotsOffset s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) =
      some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold c12WotsPkCopyStep c12WotsPkCopyBody mstoreE mloadE
  change (match execStmtList [] st
      [Stmt.mstore (addE (u 0x40) (shlE (u 5) (v "i")))
        (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))] with
    | .continue s' => (s'.world.memory 0x00).val
    | _ => (st.world.memory 0x00).val) = (s.world.memory 0x00).val
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st
      (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val 0x00).val =
    (s.world.memory 0x00).val
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by omega)]

/-- A bounded WOTS-PK copy-loop iteration copies the generated chain word from
`0x80 + 32 * idx` into the final Keccak preimage slot `0x40 + 32 * idx`. -/
theorem c12WotsPkCopyStep_copies_chain_word
    (s : RuntimeState) (idx : Nat) (hidx : idx < 67) :
    ((c12WotsPkCopyStep
      { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
      (0x40 + 32 * idx)).val =
      (s.world.memory (0x80 + 32 * idx)).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
      some (0x40 + 32 * idx) :=
    evalC12WotsOffset s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) =
      some (0x80 + 32 * idx) :=
    evalC12WotsOffset s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) =
      some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold c12WotsPkCopyStep c12WotsPkCopyBody mstoreE mloadE
  change (match execStmtList [] st
      [Stmt.mstore (addE (u 0x40) (shlE (u 5) (v "i")))
        (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))] with
    | .continue s' => (s'.world.memory (0x40 + 32 * idx)).val
    | _ => (st.world.memory (0x40 + 32 * idx)).val) =
      (s.world.memory (0x80 + 32 * idx)).val
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st
      (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val (0x40 + 32 * idx)).val =
    (s.world.memory (0x80 + 32 * idx)).val
  rw [MemoryKit.memUpdate_same]
  exact Nat.mod_eq_of_lt (s.world.memory (0x80 + 32 * idx)).isLt

/-- A bounded WOTS-PK copy-loop iteration preserves every other final-Keccak
chain slot. -/
theorem c12WotsPkCopyStep_preserves_other_chain_word
    (s : RuntimeState) (idx j : Nat) (hidx : idx < 67)
    (hne : idx ≠ j) :
    ((c12WotsPkCopyStep
      { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
      (0x40 + 32 * j)).val =
      (s.world.memory (0x40 + 32 * j)).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
      some (0x40 + 32 * idx) :=
    evalC12WotsOffset s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) =
      some (0x80 + 32 * idx) :=
    evalC12WotsOffset s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) =
      some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold c12WotsPkCopyStep c12WotsPkCopyBody mstoreE mloadE
  change (match execStmtList [] st
      [Stmt.mstore (addE (u 0x40) (shlE (u 5) (v "i")))
        (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))] with
    | .continue s' => (s'.world.memory (0x40 + 32 * j)).val
    | _ => (st.world.memory (0x40 + 32 * j)).val) =
      (s.world.memory (0x40 + 32 * j)).val
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st
      (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val (0x40 + 32 * j)).val =
    (s.world.memory (0x40 + 32 * j)).val
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by
    intro haddr
    apply hne
    omega)]

/-- Generic frame form for one WOTS-PK copy iteration: only the destination
`0x40 + 32 * idx` can change. -/
theorem c12WotsPkCopyStep_preserves_memory_addr_of_ne
    (s : RuntimeState) (idx addr : Nat) (hidx : idx < 67)
    (hne : 0x40 + 32 * idx ≠ addr) :
    ((c12WotsPkCopyStep
      { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
      addr).val =
      (s.world.memory addr).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
      some (0x40 + 32 * idx) :=
    evalC12WotsOffset s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) =
      some (0x80 + 32 * idx) :=
    evalC12WotsOffset s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) =
      some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold c12WotsPkCopyStep c12WotsPkCopyBody mstoreE mloadE
  change (match execStmtList [] st
      [Stmt.mstore (addE (u 0x40) (shlE (u 5) (v "i")))
        (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))] with
    | .continue s' => (s'.world.memory addr).val
    | _ => (st.world.memory addr).val) =
      (s.world.memory addr).val
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st
      (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val addr).val =
    (s.world.memory addr).val
  rw [MemoryKit.memUpdate_diff _ _ _ _ (fun haddr => hne haddr.symm)]

/-- The full 45-step WOTS-PK copy loop moves every generated chain word from
`0x80 + 32 * j` into the final Keccak preimage slot `0x40 + 32 * j`. -/
theorem c12WotsPkCopyLoop_copies_chain_word
    (s : RuntimeState) (j : Nat) (hj : j < 45) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 45).world.memory
      (0x40 + 32 * j)).val =
      (s.world.memory (0x80 + 32 * j)).val := by
  have htarget :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_memory_val_eq_step_at_of_suffix_preserves
      "i" c12WotsPkCopyStep (0x40 + 32 * j) s 0 45 j hj
      (fun s idx hgt hlt =>
        c12WotsPkCopyStep_preserves_other_chain_word s idx j (by omega) (by omega))
  have hstep :=
    c12WotsPkCopyStep_copies_chain_word
      (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 j)
      j (by omega)
  have hsrc :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 j).world.memory
        (0x80 + 32 * j)).val =
        (s.world.memory (0x80 + 32 * j)).val :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_memory_val_range
      "i" c12WotsPkCopyStep (0x80 + 32 * j) (fun idx => idx < j)
      (fun s idx hidx =>
        c12WotsPkCopyStep_preserves_memory_addr_of_ne s idx (0x80 + 32 * j)
          (by omega) (by omega))
      s 0 j
      (fun i _ hi2 => by omega)
  calc
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 45).world.memory
        (0x40 + 32 * j)).val
        = ((c12WotsPkCopyStep
              (have __src :=
                SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 j
              { world := __src.world
                bindings :=
                  bindValue
                    (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 j).bindings
                    "i" (wordNormalize (0 + j))
                selector := __src.selector })).world.memory
            (0x40 + 32 * j)).val := htarget
    _ = ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 j).world.memory
          (0x80 + 32 * j)).val := by
        simpa [Nat.zero_add] using hstep
    _ = (s.world.memory (0x80 + 32 * j)).val := hsrc

/-- Value-parametric form of `c12WotsPkCopyLoop_copies_chain_word`, convenient
for threading parsed/spec WOTS chain-end words into the final C12 WOTS-PK
Keccak preimage. -/
theorem c12WotsPkCopyLoop_copied_cells
    (s : RuntimeState) (cells : Nat → Nat)
    (hSrc : ∀ j, j < 45 → (s.world.memory (0x80 + 32 * j)).val = cells j) :
    ∀ j, (hj : j < 45) →
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 45).world.memory
        (0x40 + 32 * j)).val = cells j := by
  intro j hj
  rw [c12WotsPkCopyLoop_copies_chain_word s j hj]
  exact hSrc j hj

/-- The WOTS-PK copy loop writes only the chain-word destination range, so it
preserves the WOTS address slot at `0x20`. -/
theorem c12WotsPkCopyLoop_preserves_pkAdrs_slot
    (s : RuntimeState) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 45).world.memory
      0x20).val =
      (s.world.memory 0x20).val :=
  SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_memory_val_range
    "i" c12WotsPkCopyStep 0x20 (fun idx => idx < 45)
    (fun s idx hidx =>
      c12WotsPkCopyStep_preserves_memory_addr_of_ne s idx 0x20 (by omega) (by omega))
    s 0 45
    (fun i _ hi => by omega)

/-- A bounded WOTS-PK copy-loop body execution preserves the public-seed scratch cell. -/
theorem c12WotsPkCopyBody_preserves_memory_zero_bound
    (s : RuntimeState) (idx : Nat) (hidx : idx < 45) (s'' : RuntimeState)
    (hExec : execStmtList []
      { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      c12WotsPkCopyBody = .continue s'') :
    (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  have hstep := execC12WotsPkCopyBody
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  rw [hExec] at hstep
  have hout :
      (s''.world.memory 0x00).val =
        ((c12WotsPkCopyStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
          0x00).val := by
    exact congrArg
      (fun r => match r with
        | .continue st => (st.world.memory 0x00).val
        | _ => 0) hstep
  rw [hout]
  exact c12WotsPkCopyStep_preserves_memory_zero_bound s idx (by omega)

def c12XmssBody : List Stmt := [
  .letVar "sibling" (andE (cdload (addE (v "authPtr") (shlE (u 4) (v "h")))) (u N_MASK)),
  .letVar "parentIdx" (shrE (u 1) (v "mIdx")),
  mstore 0x20 (orE (v "xmssBase") (orE (shlE (u 32) (addE (v "h") (u 1))) (v "parentIdx"))),
  .letVar "s" (shlE (u 5) (andE (v "mIdx") (u 1))),
  mstoreE (xorE (u 0x40) (v "s")) (v "merkleNode"),
  mstoreE (xorE (u 0x60) (v "s")) (v "sibling"),
  .assignVar "merkleNode" (andE (keccak 0x00 0x80) (u N_MASK)),
  .assignVar "mIdx" (v "parentIdx")
]

def c12XmssStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12XmssBody with
  | .continue s' => s'
  | _ => st

theorem execC12XmssBody (st : RuntimeState) :
    execStmtList [] st c12XmssBody = .continue (c12XmssStep st) := by
  unfold c12XmssStep c12XmssBody mstore mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "sibling" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "parentIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "s" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "mIdx" _ _ rfl)]
  rfl

/-- One C12 XMSS step does not rebind `"authOff"`. -/
theorem c12XmssStep_preserves_authOff (st : RuntimeState) :
    lookupValue (c12XmssStep st).bindings "authOff" =
      lookupValue st.bindings "authOff" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "authOff" c12XmssBody st (c12XmssStep st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12XmssBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "sibling" "authOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "parentIdx" "authOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "authOff" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "s" "authOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "authOff" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "authOff" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
          _ _ "merkleNode" "authOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
          _ _ "mIdx" "authOff" _ (by decide) hexec)
    (execC12XmssBody st)

/-- One C12 XMSS step preserves `"sigBase"`. -/
theorem c12XmssStep_preserves_sigBase (st : RuntimeState) :
    lookupValue (c12XmssStep st).bindings "sigBase" =
      lookupValue st.bindings "sigBase" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "sigBase" c12XmssBody st (c12XmssStep st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12XmssBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "sibling" "sigBase" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "parentIdx" "sigBase" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "sigBase" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "s" "sigBase" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "sigBase" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "sigBase" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
          _ _ "merkleNode" "sigBase" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
          _ _ "mIdx" "sigBase" _ (by decide) hexec)
    (execC12XmssBody st)

/-- One C12 XMSS step preserves `"curTree"`. -/
theorem c12XmssStep_preserves_curTree (st : RuntimeState) :
    lookupValue (c12XmssStep st).bindings "curTree" =
      lookupValue st.bindings "curTree" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "curTree" c12XmssBody st (c12XmssStep st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12XmssBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "sibling" "curTree" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "parentIdx" "curTree" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "curTree" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "s" "curTree" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "curTree" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "curTree" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
          _ _ "merkleNode" "curTree" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
          _ _ "mIdx" "curTree" _ (by decide) hexec)
    (execC12XmssBody st)

def c12LayerBody : List Stmt := [
  .letVar "wotsBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 96) (v "curLeaf"))),
  .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")),
  .letVar "csum" (u 0),
  .forEach "i" (u 42) c12WotsMessageBody,
  .letVar "csumShifted" (shlE (u 7) (v "csum")),
  .forEach "j" (u 3) c12WotsChecksumBody,
  .letVar "pkAdrs" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (orE (shlE (u 128) (u 1)) (shlE (u 96) (v "curLeaf")))),
  mstore 0x20 (v "pkAdrs"),
  .forEach "i" (u 45) c12WotsPkCopyBody,
  .letVar "wotsPk" (andE (keccak 0x00 0x5E0) (u N_MASK)),
  .letVar "authOff" (addE (v "sigOff") (u 720)),
  .letVar "authPtr" (addE (v "sigBase") (v "authOff")),
  .letVar "xmssBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 128) (u 2))),
  .letVar "merkleNode" (v "wotsPk"),
  .letVar "mIdx" (v "curLeaf"),
  .forEach "h" (u 4) c12XmssBody,
  .assignVar "currentNode" (v "merkleNode"),
  .assignVar "sigOff" (addE (v "authOff") (u 64)),
  .assignVar "curLeaf" (andE (v "curTree") (u 0xF)),
  .assignVar "curTree" (shrE (u 4) (v "curTree"))
]

def c12LayerStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12LayerBody with
  | .continue s' => s'
  | _ => st

theorem execC12LayerBody (st : RuntimeState) :
    execStmtList [] st c12LayerBody = .continue (c12LayerStep st) := by
  unfold c12LayerStep c12LayerBody mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "wotsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 42) c12WotsMessageBody _ (wordNormalize 42)
      c12WotsMessageStep rfl execC12WotsMessageBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csumShifted" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "j" (u 3) c12WotsChecksumBody _ (wordNormalize 3)
      c12WotsChecksumStep rfl execC12WotsChecksumBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 45) c12WotsPkCopyBody _ (wordNormalize 45)
      c12WotsPkCopyStep rfl execC12WotsPkCopyBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "h" (u 4) c12XmssBody _ (wordNormalize 4)
      c12XmssStep rfl execC12XmssBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "sigOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curTree" _ _ rfl)]
  rfl

def c12LayerBodyBeforeCurrentNode : List Stmt :=
  [
    .letVar "wotsBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 96) (v "curLeaf"))),
    .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")),
    .letVar "csum" (u 0),
    .forEach "i" (u 42) c12WotsMessageBody,
    .letVar "csumShifted" (shlE (u 7) (v "csum")),
    .forEach "j" (u 3) c12WotsChecksumBody,
    .letVar "pkAdrs" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (orE (shlE (u 128) (u 1)) (shlE (u 96) (v "curLeaf")))),
    mstore 0x20 (v "pkAdrs"),
    .forEach "i" (u 45) c12WotsPkCopyBody,
    .letVar "wotsPk" (andE (keccak 0x00 0x5E0) (u N_MASK)),
    .letVar "authOff" (addE (v "sigOff") (u 720)),
    .letVar "authPtr" (addE (v "sigBase") (v "authOff")),
    .letVar "xmssBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 128) (u 2))),
    .letVar "merkleNode" (v "wotsPk"),
    .letVar "mIdx" (v "curLeaf"),
    .forEach "h" (u 4) c12XmssBody
  ]

def c12LayerBodyBeforeXmssLoop : List Stmt :=
  [
    .letVar "wotsBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 96) (v "curLeaf"))),
    .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")),
    .letVar "csum" (u 0),
    .forEach "i" (u 42) c12WotsMessageBody,
    .letVar "csumShifted" (shlE (u 7) (v "csum")),
    .forEach "j" (u 3) c12WotsChecksumBody,
    .letVar "pkAdrs" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (orE (shlE (u 128) (u 1)) (shlE (u 96) (v "curLeaf")))),
    mstore 0x20 (v "pkAdrs"),
    .forEach "i" (u 45) c12WotsPkCopyBody,
    .letVar "wotsPk" (andE (keccak 0x00 0x5E0) (u N_MASK)),
    .letVar "authOff" (addE (v "sigOff") (u 720)),
    .letVar "authPtr" (addE (v "sigBase") (v "authOff")),
    .letVar "xmssBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 128) (u 2))),
    .letVar "merkleNode" (v "wotsPk"),
    .letVar "mIdx" (v "curLeaf")
  ]

def c12LayerBodyBeforeXmssNode : List Stmt :=
  [
    .letVar "wotsBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 96) (v "curLeaf"))),
    .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")),
    .letVar "csum" (u 0),
    .forEach "i" (u 42) c12WotsMessageBody,
    .letVar "csumShifted" (shlE (u 7) (v "csum")),
    .forEach "j" (u 3) c12WotsChecksumBody,
    .letVar "pkAdrs" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (orE (shlE (u 128) (u 1)) (shlE (u 96) (v "curLeaf")))),
    mstore 0x20 (v "pkAdrs"),
    .forEach "i" (u 45) c12WotsPkCopyBody,
    .letVar "wotsPk" (andE (keccak 0x00 0x5E0) (u N_MASK)),
    .letVar "authOff" (addE (v "sigOff") (u 720)),
    .letVar "authPtr" (addE (v "sigBase") (v "authOff")),
    .letVar "xmssBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 128) (u 2)))
  ]

def c12LayerBodyBeforeAuthOff : List Stmt :=
  [
    .letVar "wotsBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 96) (v "curLeaf"))),
    .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")),
    .letVar "csum" (u 0),
    .forEach "i" (u 42) c12WotsMessageBody,
    .letVar "csumShifted" (shlE (u 7) (v "csum")),
    .forEach "j" (u 3) c12WotsChecksumBody,
    .letVar "pkAdrs" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (orE (shlE (u 128) (u 1)) (shlE (u 96) (v "curLeaf")))),
    mstore 0x20 (v "pkAdrs"),
    .forEach "i" (u 45) c12WotsPkCopyBody,
    .letVar "wotsPk" (andE (keccak 0x00 0x5E0) (u N_MASK))
  ]

def c12LayerBodyBeforeWotsPk : List Stmt :=
  [
    .letVar "wotsBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 96) (v "curLeaf"))),
    .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")),
    .letVar "csum" (u 0),
    .forEach "i" (u 42) c12WotsMessageBody,
    .letVar "csumShifted" (shlE (u 7) (v "csum")),
    .forEach "j" (u 3) c12WotsChecksumBody,
    .letVar "pkAdrs" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (orE (shlE (u 128) (u 1)) (shlE (u 96) (v "curLeaf")))),
    mstore 0x20 (v "pkAdrs"),
    .forEach "i" (u 45) c12WotsPkCopyBody
  ]

def c12LayerBodyBeforeWotsPkCopy : List Stmt :=
  [
    .letVar "wotsBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 96) (v "curLeaf"))),
    .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")),
    .letVar "csum" (u 0),
    .forEach "i" (u 42) c12WotsMessageBody,
    .letVar "csumShifted" (shlE (u 7) (v "csum")),
    .forEach "j" (u 3) c12WotsChecksumBody,
    .letVar "pkAdrs" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (orE (shlE (u 128) (u 1)) (shlE (u 96) (v "curLeaf")))),
    mstore 0x20 (v "pkAdrs")
  ]

def c12LayerPkAdrsExpr : Expr :=
  orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree")))
    (orE (shlE (u 128) (u 1)) (shlE (u 96) (v "curLeaf")))

def c12LayerBodyBeforePkAdrs : List Stmt :=
  [
    .letVar "wotsBase" (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree"))) (shlE (u 96) (v "curLeaf"))),
    .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")),
    .letVar "csum" (u 0),
    .forEach "i" (u 42) c12WotsMessageBody,
    .letVar "csumShifted" (shlE (u 7) (v "csum")),
    .forEach "j" (u 3) c12WotsChecksumBody
  ]

def c12LayerStateBeforePkAdrs (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12LayerBodyBeforePkAdrs with
  | .continue s' => s'
  | _ => st

theorem execC12LayerBodyBeforePkAdrs (st : RuntimeState) :
    execStmtList [] st c12LayerBodyBeforePkAdrs =
      .continue (c12LayerStateBeforePkAdrs st) := by
  unfold c12LayerStateBeforePkAdrs c12LayerBodyBeforePkAdrs
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "wotsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 42) c12WotsMessageBody _ (wordNormalize 42)
      c12WotsMessageStep rfl execC12WotsMessageBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csumShifted" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "j" (u 3) c12WotsChecksumBody _ (wordNormalize 3)
      c12WotsChecksumStep rfl execC12WotsChecksumBody)]
  rfl

/-- State after the first three WOTS setup bindings in `c12LayerBodyBeforePkAdrs`. -/
def c12LayerBeforePkAdrsMessageStart (st : RuntimeState) : RuntimeState :=
  let wotsBaseVal :=
    (evalExpr [] st
      (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree")))
        (shlE (u 96) (v "curLeaf")))).getD 0
  let stWotsBase :=
    { st with bindings := bindValue st.bindings "wotsBase" wotsBaseVal }
  let wotsPtrVal :=
    (evalExpr [] stWotsBase (addE (v "sigBase") (v "sigOff"))).getD 0
  let stWotsPtr :=
    { stWotsBase with bindings := bindValue stWotsBase.bindings "wotsPtr" wotsPtrVal }
  { stWotsPtr with bindings := bindValue stWotsPtr.bindings "csum" 0 }

/-- State after the 42 C12 WOTS message-loop iterations in `beforePkAdrs`. -/
def c12LayerBeforePkAdrsMessageEnd (st : RuntimeState) : RuntimeState :=
  SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep
    { (c12LayerBeforePkAdrsMessageStart st) with
      bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
        "i" (wordNormalize 0) }
    0 (wordNormalize 42)

/-- The named C12 message-loop end is the concrete 42-step fold. -/
theorem c12LayerBeforePkAdrsMessageEnd_eq_foldLoop42
    (st : RuntimeState) :
    c12LayerBeforePkAdrsMessageEnd st =
      SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep
        { (c12LayerBeforePkAdrsMessageStart st) with
          bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
            "i" (wordNormalize 0) }
        0 42 := by
  unfold c12LayerBeforePkAdrsMessageEnd
  have h42 : wordNormalize 42 = 42 := by
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  rw [h42]

/-- State after binding `"csumShifted"` immediately before the checksum loop. -/
def c12LayerBeforePkAdrsChecksumStart (st : RuntimeState) : RuntimeState :=
  let stMessage := c12LayerBeforePkAdrsMessageEnd st
  let csumShiftedVal :=
    (evalExpr [] stMessage (shlE (u 7) (v "csum"))).getD 0
  { stMessage with bindings := bindValue stMessage.bindings "csumShifted" csumShiftedVal }

theorem c12LayerBeforePkAdrsMessageStart_preserves_memory_zero
    (st : RuntimeState) :
    ((c12LayerBeforePkAdrsMessageStart st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rfl

theorem c12LayerBeforePkAdrsMessageStart_preserves_calldata
    (st : RuntimeState) :
    (c12LayerBeforePkAdrsMessageStart st).world.calldata =
      st.world.calldata := by
  rfl

theorem c12LayerBeforePkAdrsMessageLoopStart_preserves_calldata
    (st : RuntimeState) :
    ({ c12LayerBeforePkAdrsMessageStart st with
      bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
        "i" (wordNormalize 0) }).world.calldata =
      st.world.calldata := by
  exact c12LayerBeforePkAdrsMessageStart_preserves_calldata st

theorem c12LayerBeforePkAdrsMessageLoopStart_preserves_memory_zero
    (st : RuntimeState) :
    (({ c12LayerBeforePkAdrsMessageStart st with
      bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
        "i" (wordNormalize 0) }).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  exact c12LayerBeforePkAdrsMessageStart_preserves_memory_zero st

theorem c12LayerBeforePkAdrsChecksumLoopStart_preserves_memory_zero
    (st : RuntimeState) :
    (({ c12LayerBeforePkAdrsChecksumStart st with
      bindings := bindValue (c12LayerBeforePkAdrsChecksumStart st).bindings
        "j" (wordNormalize 0) }).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  unfold c12LayerBeforePkAdrsChecksumStart
  rw [c12LayerBeforePkAdrsMessageEnd_eq_foldLoop42]
  rw [c12WotsMessageFold_preserves_memory_zero_bound
    ({ c12LayerBeforePkAdrsMessageStart st with
      bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
        "i" (wordNormalize 0) }) 42 (by omega)]
  exact c12LayerBeforePkAdrsMessageLoopStart_preserves_memory_zero st

theorem c12LayerBeforePkAdrsChecksumLoopStart_wotsBase_eq_foldLoop42
    (st : RuntimeState) :
    lookupValue
        ({ c12LayerBeforePkAdrsChecksumStart st with
          bindings := bindValue (c12LayerBeforePkAdrsChecksumStart st).bindings
            "j" (wordNormalize 0) }).bindings
        "wotsBase" =
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep
          { c12LayerBeforePkAdrsMessageStart st with
            bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
              "i" (wordNormalize 0) }
          0 42).bindings
        "wotsBase" := by
  unfold c12LayerBeforePkAdrsChecksumStart
  rw [MemoryKit.lookupValue_bindValue_ne _ "j" "wotsBase" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "csumShifted" "wotsBase" _ (by decide)]
  rw [c12LayerBeforePkAdrsMessageEnd_eq_foldLoop42]

theorem c12LayerBeforePkAdrsChecksumLoopStart_wotsPtr_eq_foldLoop42
    (st : RuntimeState) :
    lookupValue
        ({ c12LayerBeforePkAdrsChecksumStart st with
          bindings := bindValue (c12LayerBeforePkAdrsChecksumStart st).bindings
            "j" (wordNormalize 0) }).bindings
        "wotsPtr" =
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep
          { c12LayerBeforePkAdrsMessageStart st with
            bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
              "i" (wordNormalize 0) }
          0 42).bindings
        "wotsPtr" := by
  unfold c12LayerBeforePkAdrsChecksumStart
  rw [MemoryKit.lookupValue_bindValue_ne _ "j" "wotsPtr" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "csumShifted" "wotsPtr" _ (by decide)]
  rw [c12LayerBeforePkAdrsMessageEnd_eq_foldLoop42]

theorem c12LayerBeforePkAdrsMessageStart_currentNode_eq
    (st : RuntimeState) :
    lookupValue (c12LayerBeforePkAdrsMessageStart st).bindings "currentNode" =
      lookupValue st.bindings "currentNode" := by
  unfold c12LayerBeforePkAdrsMessageStart
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "csum" "currentNode" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "wotsPtr" "currentNode" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "wotsBase" "currentNode" _ (by decide)]

theorem c12LayerBeforePkAdrsMessageStart_csum_eq
    (st : RuntimeState) :
    lookupValue (c12LayerBeforePkAdrsMessageStart st).bindings "csum" = 0 := by
  unfold c12LayerBeforePkAdrsMessageStart
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]

theorem c12LayerBeforePkAdrsMessageLoopStart_currentNode_eq
    (st : RuntimeState) :
    lookupValue
      ({ c12LayerBeforePkAdrsMessageStart st with
        bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
          "i" (wordNormalize 0) }).bindings
      "currentNode" =
      lookupValue st.bindings "currentNode" := by
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "currentNode" _ (by decide)]
  exact c12LayerBeforePkAdrsMessageStart_currentNode_eq st

theorem c12LayerBeforePkAdrsMessageLoopStart_csum_eq
    (st : RuntimeState) :
    lookupValue
      ({ c12LayerBeforePkAdrsMessageStart st with
        bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
          "i" (wordNormalize 0) }).bindings
      "csum" = 0 := by
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "csum" _ (by decide)]
  exact c12LayerBeforePkAdrsMessageStart_csum_eq st

theorem c12LayerBeforePkAdrsMessageStart_wotsBase_eq_of_eval
    (st : RuntimeState) (wotsBase : Nat)
    (hEval : evalExpr [] st
      (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree")))
        (shlE (u 96) (v "curLeaf"))) = some wotsBase) :
    lookupValue (c12LayerBeforePkAdrsMessageStart st).bindings "wotsBase" =
      wotsBase := by
  unfold c12LayerBeforePkAdrsMessageStart
  rw [hEval]
  simp only [Option.getD_some]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "csum" "wotsBase" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "wotsPtr" "wotsBase" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]

theorem c12LayerBeforePkAdrsMessageStart_wotsPtr_eq_of_eval
    (st : RuntimeState) (wotsPtr : Nat)
    (hEval : evalExpr []
      (let wotsBaseVal :=
        (evalExpr [] st
          (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree")))
            (shlE (u 96) (v "curLeaf")))).getD 0
       { st with bindings := bindValue st.bindings "wotsBase" wotsBaseVal })
      (addE (v "sigBase") (v "sigOff")) = some wotsPtr) :
    lookupValue (c12LayerBeforePkAdrsMessageStart st).bindings "wotsPtr" =
      wotsPtr := by
  unfold c12LayerBeforePkAdrsMessageStart
  simp only [hEval, Option.getD_some]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "csum" "wotsPtr" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]

theorem c12LayerBeforePkAdrsMessageLoopStart_wotsBase_eq_of_eval
    (st : RuntimeState) (wotsBase : Nat)
    (hEval : evalExpr [] st
      (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree")))
        (shlE (u 96) (v "curLeaf"))) = some wotsBase) :
    lookupValue
      ({ c12LayerBeforePkAdrsMessageStart st with
        bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
          "i" (wordNormalize 0) }).bindings
      "wotsBase" = wotsBase := by
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "wotsBase" _ (by decide)]
  exact c12LayerBeforePkAdrsMessageStart_wotsBase_eq_of_eval st wotsBase hEval

theorem c12LayerBeforePkAdrsMessageLoopStart_wotsPtr_eq_of_eval
    (st : RuntimeState) (wotsPtr : Nat)
    (hEval : evalExpr []
      (let wotsBaseVal :=
        (evalExpr [] st
          (orE (orE (shlE (u 224) (v "layer")) (shlE (u 160) (v "curTree")))
            (shlE (u 96) (v "curLeaf")))).getD 0
       { st with bindings := bindValue st.bindings "wotsBase" wotsBaseVal })
      (addE (v "sigBase") (v "sigOff")) = some wotsPtr) :
    lookupValue
      ({ c12LayerBeforePkAdrsMessageStart st with
        bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
          "i" (wordNormalize 0) }).bindings
      "wotsPtr" = wotsPtr := by
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      _ "i" "wotsPtr" _ (by decide)]
  exact c12LayerBeforePkAdrsMessageStart_wotsPtr_eq_of_eval st wotsPtr hEval

/-- The message-loop checksum accumulator remains small at every prefix from
the named `beforePkAdrs` message-loop start. -/
theorem c12LayerBeforePkAdrsMessageLoop_csum_add7_lt
    (st : RuntimeState) (j currentNode : Nat)
    (hj : j < 42)
    (hCNLt : currentNode < 2 ^ 256)
    (hCN : lookupValue st.bindings "currentNode" = currentNode) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep
          { c12LayerBeforePkAdrsMessageStart st with
            bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
              "i" (wordNormalize 0) }
          0 j).bindings
        "csum" + 7 < 2 ^ 256 := by
  let stLoop : RuntimeState :=
    { c12LayerBeforePkAdrsMessageStart st with
      bindings := bindValue (c12LayerBeforePkAdrsMessageStart st).bindings
        "i" (wordNormalize 0) }
  have hCNStart : lookupValue stLoop.bindings "currentNode" = currentNode := by
    rw [show lookupValue stLoop.bindings "currentNode" =
        lookupValue st.bindings "currentNode" from by
      simpa [stLoop] using c12LayerBeforePkAdrsMessageLoopStart_currentNode_eq st]
    exact hCN
  have hCsumStart : lookupValue stLoop.bindings "csum" = 0 := by
    simpa [stLoop] using c12LayerBeforePkAdrsMessageLoopStart_csum_eq st
  have hBound := c12WotsMessageFold_csum_bound stLoop j currentNode (by omega) hCNLt
    hCNStart hCsumStart
  simpa [stLoop] using (by omega : lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsMessageStep stLoop 0 j).bindings
        "csum" + 7 < 2 ^ 256)

/-- The `beforePkAdrs` prefix is the checksum fold over the state obtained
after the WOTS message fold and checksum-shift binding. -/
theorem c12LayerStateBeforePkAdrs_eq_checksum_fold (st : RuntimeState) :
    c12LayerStateBeforePkAdrs st =
      let stCsumShifted := c12LayerBeforePkAdrsChecksumStart st
      let stChecksumStart :=
        { stCsumShifted with bindings := bindValue stCsumShifted.bindings "j" (wordNormalize 0) }
      SphincsMinusVerifiers.ClimbLoop.foldLoop "j" c12WotsChecksumStep
        stChecksumStart 0 (wordNormalize 3) := by
  unfold c12LayerStateBeforePkAdrs c12LayerBodyBeforePkAdrs
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "wotsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 42) c12WotsMessageBody _ (wordNormalize 42)
      c12WotsMessageStep rfl execC12WotsMessageBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csumShifted" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "j" (u 3) c12WotsChecksumBody _ (wordNormalize 3)
      c12WotsChecksumStep rfl execC12WotsChecksumBody)]
  unfold c12LayerBeforePkAdrsChecksumStart c12LayerBeforePkAdrsMessageEnd
    c12LayerBeforePkAdrsMessageStart
  rfl

/-- The checksum suffix of `beforePkAdrs` preserves each message-loop cell. -/
theorem c12LayerStateBeforePkAdrs_message_cell_eq_message_end
    (st : RuntimeState) (j : Nat) (hj : j < 42) :
    ((c12LayerStateBeforePkAdrs st).world.memory (0x80 + 32 * j)).val =
      ((c12LayerBeforePkAdrsMessageEnd st).world.memory (0x80 + 32 * j)).val := by
  rw [c12LayerStateBeforePkAdrs_eq_checksum_fold]
  have h3 : wordNormalize 3 = 3 := by
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  rw [h3]
  let s : RuntimeState :=
    { c12LayerBeforePkAdrsChecksumStart st with
      bindings := bindValue (c12LayerBeforePkAdrsChecksumStart st).bindings "j" (wordNormalize 0) }
  have hpres := c12WotsChecksumLoop_preserves_message_cell s j hj
  simpa [s, c12LayerBeforePkAdrsChecksumStart] using hpres

theorem c12LayerBodyBeforeWotsPkCopy_eq_beforePkAdrs_append :
    c12LayerBodyBeforeWotsPkCopy =
      c12LayerBodyBeforePkAdrs ++
        [.letVar "pkAdrs" c12LayerPkAdrsExpr, mstore 0x20 (v "pkAdrs")] := rfl

theorem c12LayerBodyBeforeWotsPk_eq_beforeCopy_append :
    c12LayerBodyBeforeWotsPk =
      c12LayerBodyBeforeWotsPkCopy ++
        [.forEach "i" (u 45) c12WotsPkCopyBody] := rfl

def c12LayerStateBeforeWotsPkCopy (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12LayerBodyBeforeWotsPkCopy with
  | .continue s' => s'
  | _ => st

theorem execC12LayerBodyBeforeWotsPkCopy (st : RuntimeState) :
    execStmtList [] st c12LayerBodyBeforeWotsPkCopy =
      .continue (c12LayerStateBeforeWotsPkCopy st) := by
  unfold c12LayerStateBeforeWotsPkCopy c12LayerBodyBeforeWotsPkCopy mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "wotsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 42) c12WotsMessageBody _ (wordNormalize 42)
      c12WotsMessageStep rfl execC12WotsMessageBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csumShifted" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "j" (u 3) c12WotsChecksumBody _ (wordNormalize 3)
      c12WotsChecksumStep rfl execC12WotsChecksumBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

theorem c12LayerStateBeforeWotsPkCopy_pkAdrs_slot_of_eval
    (st : RuntimeState) (pkAdrs : Nat)
    (hPkAdrs : evalExpr [] (c12LayerStateBeforePkAdrs st) c12LayerPkAdrsExpr =
      some pkAdrs) :
    ((c12LayerStateBeforeWotsPkCopy st).world.memory 0x20).val =
      wordNormalize pkAdrs := by
  unfold c12LayerStateBeforeWotsPkCopy
  rw [c12LayerBodyBeforeWotsPkCopy_eq_beforePkAdrs_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforePkAdrs st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforePkAdrs st) "pkAdrs" c12LayerPkAdrsExpr pkAdrs hPkAdrs)]
  let stPk : RuntimeState :=
    { c12LayerStateBeforePkAdrs st with
      bindings := bindValue (c12LayerStateBeforePkAdrs st).bindings "pkAdrs" pkAdrs }
  have hOff : evalExpr [] stPk
      (u 0x20) = some 0x20 := by
    show some (wordNormalize 0x20) = some 0x20
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hVal : evalExpr [] stPk
      (v "pkAdrs") = some pkAdrs := by
    show some (lookupValue
      (bindValue (c12LayerStateBeforePkAdrs st).bindings "pkAdrs" pkAdrs)
      "pkAdrs") = some pkAdrs
    rw [MemoryKit.lookupValue_bindValue_self]
  have hSuffix : execStmtList [] stPk [mstore 0x20 (v "pkAdrs")] =
      .continue { stPk with
        world := { stPk.world with
          memory := MemoryKit.memUpdate stPk.world.memory 0x20 pkAdrs } } := by
    change execStmtList [] stPk (Stmt.mstore (u 0x20) (v "pkAdrs") :: []) =
      .continue { stPk with
        world := { stPk.world with
          memory := MemoryKit.memUpdate stPk.world.memory 0x20 pkAdrs } }
    rw [execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_mstore_continue stPk (u 0x20) (v "pkAdrs")
        0x20 pkAdrs hOff hVal)]
    rfl
  dsimp [stPk] at hSuffix
  rw [hSuffix]
  exact MemoryKit.mstore_then_mload_same
    (c12LayerStateBeforePkAdrs st).world.memory 0x20 pkAdrs

/-- The suffix from `beforePkAdrs` to `beforeWotsPkCopy` stores only the WOTS-PK
address at `0x20`, preserving every generated chain-end cell. -/
theorem c12LayerStateBeforeWotsPkCopy_chain_cell_eq_beforePkAdrs_of_eval
    (st : RuntimeState) (pkAdrs : Nat)
    (hPkAdrs : evalExpr [] (c12LayerStateBeforePkAdrs st) c12LayerPkAdrsExpr =
      some pkAdrs) (j : Nat) :
    ((c12LayerStateBeforeWotsPkCopy st).world.memory (0x80 + 32 * j)).val =
      ((c12LayerStateBeforePkAdrs st).world.memory (0x80 + 32 * j)).val := by
  unfold c12LayerStateBeforeWotsPkCopy
  rw [c12LayerBodyBeforeWotsPkCopy_eq_beforePkAdrs_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforePkAdrs st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforePkAdrs st) "pkAdrs" c12LayerPkAdrsExpr pkAdrs hPkAdrs)]
  let stPk : RuntimeState :=
    { c12LayerStateBeforePkAdrs st with
      bindings := bindValue (c12LayerStateBeforePkAdrs st).bindings "pkAdrs" pkAdrs }
  have hOff : evalExpr [] stPk (u 0x20) = some 0x20 := by
    show some (wordNormalize 0x20) = some 0x20
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hVal : evalExpr [] stPk (v "pkAdrs") = some pkAdrs := by
    show some (lookupValue
      (bindValue (c12LayerStateBeforePkAdrs st).bindings "pkAdrs" pkAdrs)
      "pkAdrs") = some pkAdrs
    rw [MemoryKit.lookupValue_bindValue_self]
  have hSuffix : execStmtList [] stPk [mstore 0x20 (v "pkAdrs")] =
      .continue { stPk with
        world := { stPk.world with
          memory := MemoryKit.memUpdate stPk.world.memory 0x20 pkAdrs } } := by
    change execStmtList [] stPk (Stmt.mstore (u 0x20) (v "pkAdrs") :: []) =
      .continue { stPk with
        world := { stPk.world with
          memory := MemoryKit.memUpdate stPk.world.memory 0x20 pkAdrs } }
    rw [execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_mstore_continue stPk (u 0x20) (v "pkAdrs")
        0x20 pkAdrs hOff hVal)]
    rfl
  dsimp [stPk] at hSuffix
  rw [hSuffix]
  show (MemoryKit.memUpdate (c12LayerStateBeforePkAdrs st).world.memory 0x20 pkAdrs
      (0x80 + 32 * j)).val =
    ((c12LayerStateBeforePkAdrs st).world.memory (0x80 + 32 * j)).val
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by omega)]

theorem c12LayerBodyBeforeAuthOff_eq_beforeWotsPk_append :
    c12LayerBodyBeforeAuthOff =
      c12LayerBodyBeforeWotsPk ++
        [.letVar "wotsPk" (andE (keccak 0x00 0x5E0) (u N_MASK))] := rfl

theorem c12LayerBodyBeforeXmssNode_eq_beforeAuthOff_append :
    c12LayerBodyBeforeXmssNode =
      c12LayerBodyBeforeAuthOff ++
        [ .letVar "authOff" (addE (v "sigOff") (u 720))
        , .letVar "authPtr" (addE (v "sigBase") (v "authOff"))
        , .letVar "xmssBase" (orE (orE (shlE (u 224) (v "layer"))
            (shlE (u 160) (v "curTree"))) (shlE (u 128) (u 2))) ] := rfl

def c12LayerStateBeforeAuthOff (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12LayerBodyBeforeAuthOff with
  | .continue s' => s'
  | _ => st

def c12LayerStateBeforeWotsPk (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12LayerBodyBeforeWotsPk with
  | .continue s' => s'
  | _ => st

def c12LayerStateAfterWotsPkCopyLoop (st : RuntimeState) : RuntimeState :=
  SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep
    { (c12LayerStateBeforeWotsPkCopy st) with
      bindings :=
        bindValue (c12LayerStateBeforeWotsPkCopy st).bindings "i" (wordNormalize 0) }
    0 45

theorem execC12LayerBodyBeforeWotsPk (st : RuntimeState) :
    execStmtList [] st c12LayerBodyBeforeWotsPk =
      .continue (c12LayerStateBeforeWotsPk st) := by
  unfold c12LayerStateBeforeWotsPk c12LayerBodyBeforeWotsPk mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "wotsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 42) c12WotsMessageBody _ (wordNormalize 42)
      c12WotsMessageStep rfl execC12WotsMessageBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csumShifted" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "j" (u 3) c12WotsChecksumBody _ (wordNormalize 3)
      c12WotsChecksumStep rfl execC12WotsChecksumBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 45) c12WotsPkCopyBody _ (wordNormalize 45)
      c12WotsPkCopyStep rfl execC12WotsPkCopyBody)]
  rfl

theorem c12LayerStateBeforeWotsPk_eq_copyLoop (st : RuntimeState) :
    c12LayerStateBeforeWotsPk st = c12LayerStateAfterWotsPkCopyLoop st := by
  have hcopy : execStmtList [] (c12LayerStateBeforeWotsPkCopy st)
      [.forEach "i" (u 45) c12WotsPkCopyBody] =
      .continue (c12LayerStateAfterWotsPkCopyLoop st) := by
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (u 45) c12WotsPkCopyBody _ (wordNormalize 45)
        c12WotsPkCopyStep rfl execC12WotsPkCopyBody)]
    rfl
  unfold c12LayerStateBeforeWotsPk
  rw [c12LayerBodyBeforeWotsPk_eq_beforeCopy_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeWotsPkCopy st)]
  rw [hcopy]

theorem execC12LayerBodyBeforeAuthOff (st : RuntimeState) :
    execStmtList [] st c12LayerBodyBeforeAuthOff =
      .continue (c12LayerStateBeforeAuthOff st) := by
  unfold c12LayerStateBeforeAuthOff c12LayerBodyBeforeAuthOff mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "wotsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 42) c12WotsMessageBody _ (wordNormalize 42)
      c12WotsMessageStep rfl execC12WotsMessageBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csumShifted" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "j" (u 3) c12WotsChecksumBody _ (wordNormalize 3)
      c12WotsChecksumStep rfl execC12WotsChecksumBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 45) c12WotsPkCopyBody _ (wordNormalize 45)
      c12WotsPkCopyStep rfl execC12WotsPkCopyBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rfl

/-- The final WOTS-PK binding is just the masked Keccak evaluated at the smaller
boundary immediately after the copy loop.  This avoids unfolding the whole WOTS
setup prefix when reducing `C12Layer4WotsPkBeforeAuthOffPremise`. -/
theorem c12LayerStateBeforeAuthOff_wotsPk_eq_beforeWotsPk_keccak
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeAuthOff st).bindings "wotsPk" =
      (evalExpr [] (c12LayerStateBeforeWotsPk st)
        (andE (keccak 0x00 0x5E0) (u N_MASK))).getD 0 := by
  unfold c12LayerStateBeforeAuthOff
  rw [c12LayerBodyBeforeAuthOff_eq_beforeWotsPk_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeWotsPk st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforeWotsPk st) "wotsPk" _ _ rfl)]
  change lookupValue
      (bindValue (c12LayerStateBeforeWotsPk st).bindings "wotsPk"
        ((evalExpr [] (c12LayerStateBeforeWotsPk st)
          (andE (keccak 0x00 0x5E0) (u N_MASK))).getD 0))
      "wotsPk" =
    (evalExpr [] (c12LayerStateBeforeWotsPk st)
      (andE (keccak 0x00 0x5E0) (u N_MASK))).getD 0
  rw [MemoryKit.lookupValue_bindValue_self]

theorem c12WotsPkCopyLoop_preserves_pkAdrs_slot_value
    (s : RuntimeState) (pkAdrs : Nat)
    (hpkAdrs : (s.world.memory 0x20).val = pkAdrs) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" c12WotsPkCopyStep s 0 45).world.memory
      0x20).val = pkAdrs := by
  rw [c12WotsPkCopyLoop_preserves_pkAdrs_slot, hpkAdrs]

/-- Every statement before the final C12 WOTS-PK binding preserves the
public-seed scratch cell. -/
theorem c12LayerBodyBeforeWotsPk_preserves_memory_zero_body :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12LayerBodyBeforeWotsPk →
      execStmt [] s stmt = .continue s'' →
      (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  intro s s'' stmt hmem hexec
  simp only [c12LayerBodyBeforeWotsPk, mstore, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsBase" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsPtr" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "csum" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
      "i" 0x00 (u 42) c12WotsMessageBody (fun idx => idx < 42) s s''
      (fun st idx hidx out hbody =>
        c12WotsMessageBody_preserves_memory_zero_bound st idx hidx out hbody)
      (by
        intro bound i hcount _ hi
        cases hcount
        exact hi)
      hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "csumShifted" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
      "j" 0x00 (u 3) c12WotsChecksumBody (fun idx => idx < 3) s s''
      (fun st idx hidx out hbody =>
        c12WotsChecksumBody_preserves_memory_zero_bound st idx hidx out hbody)
      (by
        intro bound i hcount _ hi
        cases hcount
        exact hi)
      hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "pkAdrs" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 (u 0x20) (v "pkAdrs")
      (by
        intro ro rv hoff _
        change some 0x20 = some ro at hoff
        injection hoff with hro
        subst ro
        omega)
      hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
      "i" 0x00 (u 45) c12WotsPkCopyBody (fun idx => idx < 45) s s''
      (fun st idx hidx out hbody =>
        c12WotsPkCopyBody_preserves_memory_zero_bound st idx hidx out hbody)
      (by
        intro bound i hcount _ hi
        cases hcount
        exact hi)
      hexec

/-- Every statement before the WOTS-PK copy loop preserves the public-seed
scratch cell. -/
theorem c12LayerBodyBeforeWotsPkCopy_preserves_memory_zero_body :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12LayerBodyBeforeWotsPkCopy →
      execStmt [] s stmt = .continue s'' →
      (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  intro s s'' stmt hmem hexec
  exact c12LayerBodyBeforeWotsPk_preserves_memory_zero_body s s'' stmt
    (by
      simp only [c12LayerBodyBeforeWotsPk, c12LayerBodyBeforeWotsPkCopy,
        List.mem_cons, List.not_mem_nil, or_false] at *
      tauto)
    hexec

/-- The cutpoint immediately before the WOTS-PK copy loop preserves the
public-seed scratch cell. -/
theorem c12LayerStateBeforeWotsPkCopy_preserves_memory_zero
    (st : RuntimeState) :
    ((c12LayerStateBeforeWotsPkCopy st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  exact SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 c12LayerBodyBeforeWotsPkCopy st (c12LayerStateBeforeWotsPkCopy st)
    c12LayerBodyBeforeWotsPkCopy_preserves_memory_zero_body
    (execC12LayerBodyBeforeWotsPkCopy st)

/-- The smaller cutpoint immediately before binding `"wotsPk"` preserves the
public-seed scratch cell. -/
theorem c12LayerStateBeforeWotsPk_preserves_memory_zero
    (st : RuntimeState) :
    ((c12LayerStateBeforeWotsPk st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  exact SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 c12LayerBodyBeforeWotsPk st (c12LayerStateBeforeWotsPk st)
    c12LayerBodyBeforeWotsPk_preserves_memory_zero_body
    (execC12LayerBodyBeforeWotsPk st)

private theorem lookup_match_execStmtList_nil
    (fallback st : RuntimeState) (key : String) :
    lookupValue
        (match execStmtList [] st ([] : List Stmt) with
         | .continue s' => s'
         | _ => fallback).bindings key =
      lookupValue st.bindings key := rfl

private theorem c12LayerStateBeforeAuthOff_preserves_lookup_of_fresh
    (key : String)
    (hWotsBase : "wotsBase" ≠ key)
    (hWotsPtr : "wotsPtr" ≠ key)
    (hCsum : "csum" ≠ key)
    (hI : "i" ≠ key)
    (hDigit : "digit" ≠ key)
    (hVal : "val" ≠ key)
    (hChainBase : "chainBase" ≠ key)
    (hSteps : "steps" ≠ key)
    (hS : "s" ≠ key)
    (hCsumShifted : "csumShifted" ≠ key)
    (hJ : "j" ≠ key)
    (hPkAdrs : "pkAdrs" ≠ key)
    (hWotsPk : "wotsPk" ≠ key)
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeAuthOff st).bindings key =
      lookupValue st.bindings key := by
  exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    key c12LayerBodyBeforeAuthOff st (c12LayerStateBeforeAuthOff st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12LayerBodyBeforeAuthOff, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsBase" key _ hWotsBase hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPtr" key _ hWotsPtr hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csum" key _ hCsum hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" key _ _ _ _ hI
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsMessageBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" key _ hDigit hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                _ _ "csum" key _ hCsum hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" key _ hVal hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" key _ hChainBase hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" key _ hSteps hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" key _ _ _ _ hS
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ key _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ key _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" key _ hVal hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ key _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csumShifted" key _ hCsumShifted hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "j" key _ _ _ _ hJ
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsChecksumBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" key _ hDigit hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "i" key _ hI hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" key _ hVal hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" key _ hChainBase hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" key _ hSteps hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" key _ _ _ _ hS
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ key _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ key _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" key _ hVal hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ key _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "pkAdrs" key _ hPkAdrs hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ key _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" key _ _ _ _ hI
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsPkCopyBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            subst hmem
            exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
              _ _ key _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPk" key _ hWotsPk hexec)
    (execC12LayerBodyBeforeAuthOff st)

/-- The WOTS message/checksum prefix before the WOTS-PK address binding does
not rebind any key fresh for that prefix. -/
theorem c12LayerStateBeforePkAdrs_preserves_lookup_of_fresh
    (key : String)
    (hWotsBase : "wotsBase" ≠ key)
    (hWotsPtr : "wotsPtr" ≠ key)
    (hCsum : "csum" ≠ key)
    (hI : "i" ≠ key)
    (hDigit : "digit" ≠ key)
    (hVal : "val" ≠ key)
    (hChainBase : "chainBase" ≠ key)
    (hSteps : "steps" ≠ key)
    (hS : "s" ≠ key)
    (hCsumShifted : "csumShifted" ≠ key)
    (hJ : "j" ≠ key)
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforePkAdrs st).bindings key =
      lookupValue st.bindings key := by
  exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    key c12LayerBodyBeforePkAdrs st (c12LayerStateBeforePkAdrs st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12LayerBodyBeforePkAdrs, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsBase" key _ hWotsBase hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPtr" key _ hWotsPtr hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csum" key _ hCsum hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" key _ _ _ _ hI
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsMessageBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" key _ hDigit hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                _ _ "csum" key _ hCsum hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" key _ hVal hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" key _ hChainBase hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" key _ hSteps hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" key _ _ _ _ hS
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ key _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ key _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" key _ hVal hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ key _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csumShifted" key _ hCsumShifted hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "j" key _ _ _ _ hJ
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsChecksumBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" key _ hDigit hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "i" key _ hI hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" key _ hVal hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" key _ hChainBase hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" key _ hSteps hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" key _ _ _ _ hS
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ key _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ key _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" key _ hVal hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ key _ _ hexec)
          hexec)
    (execC12LayerBodyBeforePkAdrs st)

theorem c12LayerStateBeforePkAdrs_layer_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforePkAdrs st).bindings "layer" =
      lookupValue st.bindings "layer" := by
  exact c12LayerStateBeforePkAdrs_preserves_lookup_of_fresh
    "layer" (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) st

theorem c12LayerStateBeforePkAdrs_curTree_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforePkAdrs st).bindings "curTree" =
      lookupValue st.bindings "curTree" := by
  exact c12LayerStateBeforePkAdrs_preserves_lookup_of_fresh
    "curTree" (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) st

theorem c12LayerStateBeforePkAdrs_curLeaf_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforePkAdrs st).bindings "curLeaf" =
      lookupValue st.bindings "curLeaf" := by
  exact c12LayerStateBeforePkAdrs_preserves_lookup_of_fresh
    "curLeaf" (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) st

/-- The WOTS setup prefix before `"authOff"` does not rebind `"sigOff"`. -/
theorem c12LayerStateBeforeAuthOff_sigOff_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeAuthOff st).bindings "sigOff" =
      lookupValue st.bindings "sigOff" := by
  exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "sigOff" c12LayerBodyBeforeAuthOff st (c12LayerStateBeforeAuthOff st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12LayerBodyBeforeAuthOff, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsBase" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPtr" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csum" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" "sigOff" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsMessageBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                _ _ "csum" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" "sigOff" _ _ _ _ (by decide)
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigOff" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigOff" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" "sigOff" _ (by decide) hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ "sigOff" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csumShifted" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "j" "sigOff" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsChecksumBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "i" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" "sigOff" _ _ _ _ (by decide)
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigOff" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigOff" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" "sigOff" _ (by decide) hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ "sigOff" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "pkAdrs" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "sigOff" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" "sigOff" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsPkCopyBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            subst hmem
            exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
              _ _ "sigOff" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPk" "sigOff" _ (by decide) hexec)
    (execC12LayerBodyBeforeAuthOff st)

/-- The WOTS setup prefix before `"authOff"` does not rebind `"sigBase"`. -/
theorem c12LayerStateBeforeAuthOff_sigBase_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeAuthOff st).bindings "sigBase" =
      lookupValue st.bindings "sigBase" := by
  exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "sigBase" c12LayerBodyBeforeAuthOff st (c12LayerStateBeforeAuthOff st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12LayerBodyBeforeAuthOff, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsBase" "sigBase" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPtr" "sigBase" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csum" "sigBase" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" "sigBase" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsMessageBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                _ _ "csum" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" "sigBase" _ _ _ _ (by decide)
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigBase" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigBase" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" "sigBase" _ (by decide) hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ "sigBase" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csumShifted" "sigBase" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "j" "sigBase" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsChecksumBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "i" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" "sigBase" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" "sigBase" _ _ _ _ (by decide)
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigBase" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigBase" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" "sigBase" _ (by decide) hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ "sigBase" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "pkAdrs" "sigBase" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "sigBase" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" "sigBase" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsPkCopyBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            subst hmem
            exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
              _ _ "sigBase" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPk" "sigBase" _ (by decide) hexec)
    (execC12LayerBodyBeforeAuthOff st)

/-- The WOTS setup prefix before `"authOff"` does not rebind `"layer"`. -/
theorem c12LayerStateBeforeAuthOff_layer_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeAuthOff st).bindings "layer" =
      lookupValue st.bindings "layer" := by
  exact c12LayerStateBeforeAuthOff_preserves_lookup_of_fresh
    "layer" (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) st

/-- The WOTS setup prefix before `"authOff"` does not rebind `"curTree"`. -/
theorem c12LayerStateBeforeAuthOff_curTree_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeAuthOff st).bindings "curTree" =
      lookupValue st.bindings "curTree" := by
  exact c12LayerStateBeforeAuthOff_preserves_lookup_of_fresh
    "curTree" (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) st

theorem c12LayerBodyBeforeXmssLoop_eq_beforeNode_append :
    c12LayerBodyBeforeXmssLoop =
      c12LayerBodyBeforeXmssNode ++
        [.letVar "merkleNode" (v "wotsPk"), .letVar "mIdx" (v "curLeaf")] := rfl

theorem c12LayerBodyBeforeCurrentNode_eq_beforeXmssLoop_append_xmss :
    c12LayerBodyBeforeCurrentNode =
      c12LayerBodyBeforeXmssLoop ++ [.forEach "h" (u 4) c12XmssBody] := rfl

def c12LayerStateBeforeXmssNode (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12LayerBodyBeforeXmssNode with
  | .continue s' => s'
  | _ => st

theorem execC12LayerBodyBeforeXmssNode (st : RuntimeState) :
    execStmtList [] st c12LayerBodyBeforeXmssNode =
      .continue (c12LayerStateBeforeXmssNode st) := by
  unfold c12LayerStateBeforeXmssNode c12LayerBodyBeforeXmssNode mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "wotsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 42) c12WotsMessageBody _ (wordNormalize 42)
      c12WotsMessageStep rfl execC12WotsMessageBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csumShifted" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "j" (u 3) c12WotsChecksumBody _ (wordNormalize 3)
      c12WotsChecksumStep rfl execC12WotsChecksumBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 45) c12WotsPkCopyBody _ (wordNormalize 45)
      c12WotsPkCopyStep rfl execC12WotsPkCopyBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  rfl

/-- At the pre-XMSS-node boundary, `"authOff"` is the incoming `"sigOff"` plus
the C12 WOTS byte span. -/
theorem c12LayerStateBeforeXmssNode_authOff_eq_sigOff
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssNode st).bindings "authOff" =
      (Verity.Core.Uint256.ofNat (lookupValue st.bindings "sigOff") +
        Verity.Core.Uint256.ofNat (wordNormalize 720)).val := by
  unfold c12LayerStateBeforeXmssNode
  rw [c12LayerBodyBeforeXmssNode_eq_beforeAuthOff_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeAuthOff st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforeAuthOff st) "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue
            (bindValue (c12LayerStateBeforeAuthOff st).bindings "authOff"
              ((Verity.Core.Uint256.ofNat
                    (lookupValue (c12LayerStateBeforeAuthOff st).bindings "sigOff") +
                  Verity.Core.Uint256.ofNat (wordNormalize 720)).val))
            "authPtr" _)
          "xmssBase" _)
        "authOff" =
      (Verity.Core.Uint256.ofNat (lookupValue st.bindings "sigOff") +
        Verity.Core.Uint256.ofNat (wordNormalize 720)).val
  rw [MemoryKit.lookupValue_bindValue_ne _ "xmssBase" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "authPtr" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [c12LayerStateBeforeAuthOff_sigOff_eq]

/-- At the pre-XMSS-node boundary, `"authPtr"` is the signature base plus the
incoming `"sigOff"` advanced over the WOTS span. -/
theorem c12LayerStateBeforeXmssNode_authPtr_eq_sigBase_sigOff
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssNode st).bindings "authPtr" =
      (Verity.Core.Uint256.ofNat (lookupValue st.bindings "sigBase") +
        Verity.Core.Uint256.ofNat
          ((Verity.Core.Uint256.ofNat (lookupValue st.bindings "sigOff") +
            Verity.Core.Uint256.ofNat (wordNormalize 720)).val)).val := by
  unfold c12LayerStateBeforeXmssNode
  rw [c12LayerBodyBeforeXmssNode_eq_beforeAuthOff_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeAuthOff st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforeAuthOff st) "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue
            (bindValue (c12LayerStateBeforeAuthOff st).bindings "authOff"
              ((Verity.Core.Uint256.ofNat
                    (lookupValue (c12LayerStateBeforeAuthOff st).bindings "sigOff") +
                  Verity.Core.Uint256.ofNat (wordNormalize 720)).val))
            "authPtr"
            ((Verity.Core.Uint256.ofNat
                  (lookupValue
                    (bindValue (c12LayerStateBeforeAuthOff st).bindings "authOff"
                      ((Verity.Core.Uint256.ofNat
                            (lookupValue (c12LayerStateBeforeAuthOff st).bindings "sigOff") +
                          Verity.Core.Uint256.ofNat (wordNormalize 720)).val))
                    "sigBase") +
                Verity.Core.Uint256.ofNat
                  (lookupValue
                    (bindValue (c12LayerStateBeforeAuthOff st).bindings "authOff"
                      ((Verity.Core.Uint256.ofNat
                            (lookupValue (c12LayerStateBeforeAuthOff st).bindings "sigOff") +
                          Verity.Core.Uint256.ofNat (wordNormalize 720)).val))
                    "authOff")).val))
          "xmssBase" _)
        "authPtr" =
      (Verity.Core.Uint256.ofNat (lookupValue st.bindings "sigBase") +
        Verity.Core.Uint256.ofNat
          ((Verity.Core.Uint256.ofNat (lookupValue st.bindings "sigOff") +
            Verity.Core.Uint256.ofNat (wordNormalize 720)).val)).val
  rw [MemoryKit.lookupValue_bindValue_ne _ "xmssBase" "authPtr" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [MemoryKit.lookupValue_bindValue_ne _ "authOff" "sigBase" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [c12LayerStateBeforeAuthOff_sigBase_eq]
  rw [c12LayerStateBeforeAuthOff_sigOff_eq]

/-- The pre-XMSS-node address setup runs after `"wotsPk"` has been computed and
does not change that binding. -/
theorem c12LayerStateBeforeXmssNode_wotsPk_eq_beforeAuthOff
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk" =
      lookupValue (c12LayerStateBeforeAuthOff st).bindings "wotsPk" := by
  unfold c12LayerStateBeforeXmssNode
  rw [c12LayerBodyBeforeXmssNode_eq_beforeAuthOff_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeAuthOff st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforeAuthOff st) "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue
            (bindValue (c12LayerStateBeforeAuthOff st).bindings "authOff" _)
            "authPtr" _)
          "xmssBase" _)
        "wotsPk" =
      lookupValue (c12LayerStateBeforeAuthOff st).bindings "wotsPk"
  rw [MemoryKit.lookupValue_bindValue_ne _ "xmssBase" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "authPtr" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "authOff" "wotsPk" _ (by decide)]

/-- At the pre-XMSS-node boundary, `"xmssBase"` is the layer/current-tree ADRS
prefix tagged as an XMSS tree address. -/
theorem c12LayerStateBeforeXmssNode_xmssBase_eq_beforeAuthOff
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssNode st).bindings "xmssBase" =
      ((Verity.Core.Uint256.ofNat
          ((Verity.Core.Uint256.ofNat
                ((Verity.Core.Uint256.ofNat (wordNormalize 224)).shl
                  (Verity.Core.Uint256.ofNat
                    (lookupValue (c12LayerStateBeforeAuthOff st).bindings "layer"))).val).or
            (Verity.Core.Uint256.ofNat
                ((Verity.Core.Uint256.ofNat (wordNormalize 160)).shl
                  (Verity.Core.Uint256.ofNat
                    (lookupValue (c12LayerStateBeforeAuthOff st).bindings "curTree"))).val)).val).or
        (Verity.Core.Uint256.ofNat
          ((Verity.Core.Uint256.ofNat (wordNormalize 128)).shl
            (Verity.Core.Uint256.ofNat (wordNormalize 2))).val)).val := by
  unfold c12LayerStateBeforeXmssNode
  rw [c12LayerBodyBeforeXmssNode_eq_beforeAuthOff_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeAuthOff st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforeAuthOff st) "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  rw [lookup_match_execStmtList_nil]
  rw [MemoryKit.lookupValue_bindValue_self]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "layer" _ (by decide)]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "curTree" _ (by decide)]

/-- The WOTS setup prefix before the XMSS-node setup does not rebind
`"curTree"`. -/
theorem c12LayerStateBeforeXmssNode_curTree_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssNode st).bindings "curTree" =
      lookupValue st.bindings "curTree" := by
  unfold c12LayerStateBeforeXmssNode
  rw [c12LayerBodyBeforeXmssNode_eq_beforeAuthOff_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeAuthOff st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforeAuthOff st) "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  rw [lookup_match_execStmtList_nil]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "curTree" _ (by decide)]
  rw [c12LayerStateBeforeAuthOff_curTree_eq]

def c12LayerStateBeforeXmssLoop (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12LayerBodyBeforeXmssLoop with
  | .continue s' => s'
  | _ => st

theorem execC12LayerBodyBeforeXmssLoop (st : RuntimeState) :
    execStmtList [] st c12LayerBodyBeforeXmssLoop =
      .continue (c12LayerStateBeforeXmssLoop st) := by
  unfold c12LayerStateBeforeXmssLoop c12LayerBodyBeforeXmssLoop mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "wotsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 42) c12WotsMessageBody _ (wordNormalize 42)
      c12WotsMessageStep rfl execC12WotsMessageBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csumShifted" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "j" (u 3) c12WotsChecksumBody _ (wordNormalize 3)
      c12WotsChecksumStep rfl execC12WotsChecksumBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 45) c12WotsPkCopyBody _ (wordNormalize 45)
      c12WotsPkCopyStep rfl execC12WotsPkCopyBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rfl

/-- Every statement in the WOTS setup prefix preserves the public-seed scratch cell. -/
theorem c12LayerBodyBeforeXmssLoop_preserves_memory_zero_body :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12LayerBodyBeforeXmssLoop →
      execStmt [] s stmt = .continue s'' →
      (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  intro s s'' stmt hmem hexec
  simp only [c12LayerBodyBeforeXmssLoop, mstore, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsBase" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsPtr" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "csum" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
      "i" 0x00 (u 42) c12WotsMessageBody (fun idx => idx < 42) s s''
      (fun st idx hidx out hbody =>
        c12WotsMessageBody_preserves_memory_zero_bound st idx hidx out hbody)
      (by
        intro bound i hcount _ hi
        cases hcount
        exact hi)
      hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "csumShifted" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
      "j" 0x00 (u 3) c12WotsChecksumBody (fun idx => idx < 3) s s''
      (fun st idx hidx out hbody =>
        c12WotsChecksumBody_preserves_memory_zero_bound st idx hidx out hbody)
      (by
        intro bound i hcount _ hi
        cases hcount
        exact hi)
      hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "pkAdrs" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 (u 0x20) (v "pkAdrs")
      (by
        intro ro rv hoff _
        change some 0x20 = some ro at hoff
        injection hoff with hro
        subst ro
        omega)
      hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
      "i" 0x00 (u 45) c12WotsPkCopyBody (fun idx => idx < 45) s s''
      (fun st idx hidx out hbody =>
        c12WotsPkCopyBody_preserves_memory_zero_bound st idx hidx out hbody)
      (by
        intro bound i hcount _ hi
        cases hcount
        exact hi)
      hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsPk" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "authOff" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "authPtr" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "xmssBase" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "merkleNode" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "mIdx" _ hexec

/-- The executable WOTS setup prefix preserves the public-seed scratch cell. -/
theorem c12LayerStateBeforeXmssLoop_preserves_memory_zero
    (st : RuntimeState) :
    ((c12LayerStateBeforeXmssLoop st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  exact SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 c12LayerBodyBeforeXmssLoop st (c12LayerStateBeforeXmssLoop st)
    c12LayerBodyBeforeXmssLoop_preserves_memory_zero_body
    (execC12LayerBodyBeforeXmssLoop st)

/-- The WOTS/XMSS setup prefix seeds the XMSS climb's `"merkleNode"` from the
computed `"wotsPk"` binding.  This is the exact executable boundary immediately
before `.forEach "h" 4 c12XmssBody`. -/
theorem c12LayerStateBeforeXmssLoop_merkleNode_eq_wotsPk
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssLoop st).bindings "merkleNode" =
      lookupValue (c12LayerStateBeforeXmssLoop st).bindings "wotsPk" := by
  unfold c12LayerStateBeforeXmssLoop
  rw [c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeXmssNode st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue (c12LayerStateBeforeXmssNode st) "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
            (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
          "mIdx"
          (lookupValue
            (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
              (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
            "curLeaf"))
        "merkleNode" =
      lookupValue
        (bindValue
          (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
            (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
          "mIdx"
          (lookupValue
            (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
              (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
            "curLeaf"))
        "wotsPk"
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "merkleNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "wotsPk" _ (by decide)]

/-- The final pre-XMSS setup bindings (`"merkleNode"` and `"mIdx"`) do not
change the already computed `"wotsPk"` value. -/
theorem c12LayerStateBeforeXmssLoop_wotsPk_eq_beforeXmssNode_wotsPk
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssLoop st).bindings "wotsPk" =
      lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk" := by
  unfold c12LayerStateBeforeXmssLoop
  rw [c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeXmssNode st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue (c12LayerStateBeforeXmssNode st) "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
            (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
          "mIdx"
          (lookupValue
            (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
              (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
            "curLeaf"))
        "wotsPk" =
      lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "wotsPk" _ (by decide)]

/-- The final pre-XMSS setup bindings (`"merkleNode"` and `"mIdx"`) do not
change the already computed `"authOff"` value. -/
theorem c12LayerStateBeforeXmssLoop_authOff_eq_beforeXmssNode_authOff
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssLoop st).bindings "authOff" =
      lookupValue (c12LayerStateBeforeXmssNode st).bindings "authOff" := by
  unfold c12LayerStateBeforeXmssLoop
  rw [c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeXmssNode st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue (c12LayerStateBeforeXmssNode st) "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
            (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
          "mIdx"
          (lookupValue
            (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
              (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
            "curLeaf"))
        "authOff" =
      lookupValue (c12LayerStateBeforeXmssNode st).bindings "authOff"
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "authOff" _ (by decide)]

/-- The final pre-XMSS setup bindings (`"merkleNode"` and `"mIdx"`) do not
change the already computed `"authPtr"` value. -/
theorem c12LayerStateBeforeXmssLoop_authPtr_eq_beforeXmssNode_authPtr
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssLoop st).bindings "authPtr" =
      lookupValue (c12LayerStateBeforeXmssNode st).bindings "authPtr" := by
  unfold c12LayerStateBeforeXmssLoop
  rw [c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeXmssNode st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue (c12LayerStateBeforeXmssNode st) "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
            (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
          "mIdx"
          (lookupValue
            (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
              (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
            "curLeaf"))
        "authPtr" =
      lookupValue (c12LayerStateBeforeXmssNode st).bindings "authPtr"
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "authPtr" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "authPtr" _ (by decide)]

/-- The final pre-XMSS setup bindings (`"merkleNode"` and `"mIdx"`) do not
change the already computed `"xmssBase"` value. -/
theorem c12LayerStateBeforeXmssLoop_xmssBase_eq_beforeXmssNode_xmssBase
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssLoop st).bindings "xmssBase" =
      lookupValue (c12LayerStateBeforeXmssNode st).bindings "xmssBase" := by
  unfold c12LayerStateBeforeXmssLoop
  rw [c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeXmssNode st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue (c12LayerStateBeforeXmssNode st) "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
            (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
          "mIdx"
          (lookupValue
            (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
              (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
            "curLeaf"))
        "xmssBase" =
      lookupValue (c12LayerStateBeforeXmssNode st).bindings "xmssBase"
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "xmssBase" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "xmssBase" _ (by decide)]

/-- The final pre-XMSS setup bindings (`"merkleNode"` and `"mIdx"`) do not
change `"curTree"`. -/
theorem c12LayerStateBeforeXmssLoop_curTree_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssLoop st).bindings "curTree" =
      lookupValue st.bindings "curTree" := by
  unfold c12LayerStateBeforeXmssLoop
  rw [c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeXmssNode st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue (c12LayerStateBeforeXmssNode st) "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
            (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
          "mIdx"
          (lookupValue
            (bindValue (c12LayerStateBeforeXmssNode st).bindings "merkleNode"
              (lookupValue (c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
            "curLeaf"))
        "curTree" =
      lookupValue st.bindings "curTree"
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "curTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "curTree" _ (by decide)]
  rw [c12LayerStateBeforeXmssNode_curTree_eq]

/-- The WOTS setup prefix before the XMSS-node setup does not rebind
`"curLeaf"`. -/
theorem c12LayerStateBeforeXmssNode_curLeaf_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssNode st).bindings "curLeaf" =
      lookupValue st.bindings "curLeaf" := by
  exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "curLeaf" c12LayerBodyBeforeXmssNode st (c12LayerStateBeforeXmssNode st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12LayerBodyBeforeXmssNode, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsBase" "curLeaf" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPtr" "curLeaf" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csum" "curLeaf" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" "curLeaf" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsMessageBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                _ _ "csum" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" "curLeaf" _ _ _ _ (by decide)
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "curLeaf" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "curLeaf" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" "curLeaf" _ (by decide) hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ "curLeaf" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csumShifted" "curLeaf" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "j" "curLeaf" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsChecksumBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "i" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" "curLeaf" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" "curLeaf" _ _ _ _ (by decide)
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "curLeaf" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "curLeaf" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" "curLeaf" _ (by decide) hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ "curLeaf" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "pkAdrs" "curLeaf" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "curLeaf" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" "curLeaf" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsPkCopyBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            subst hmem
            exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
              _ _ "curLeaf" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPk" "curLeaf" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "authOff" "curLeaf" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "authPtr" "curLeaf" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "xmssBase" "curLeaf" _ (by decide) hexec)
    (execC12LayerBodyBeforeXmssNode st)

/-- The WOTS setup prefix before the XMSS-node setup does not rebind
`"sigOff"`. -/
theorem c12LayerStateBeforeXmssNode_sigOff_eq
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssNode st).bindings "sigOff" =
      lookupValue st.bindings "sigOff" := by
  exact SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "sigOff" c12LayerBodyBeforeXmssNode st (c12LayerStateBeforeXmssNode st)
    (by
      intro s s'' stmt hmem hexec
      simp only [c12LayerBodyBeforeXmssNode, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsBase" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPtr" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csum" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" "sigOff" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsMessageBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                _ _ "csum" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" "sigOff" _ _ _ _ (by decide)
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigOff" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigOff" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" "sigOff" _ (by decide) hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ "sigOff" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "csumShifted" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "j" "sigOff" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsChecksumBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "digit" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "i" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "val" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "chainBase" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
                _ _ "steps" "sigOff" _ (by decide) hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
                "s" "sigOff" _ _ _ _ (by decide)
                (by
                  intro s s'' stmt hmem hexec
                  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with rfl | rfl | rfl
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigOff" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                      _ _ "sigOff" _ _ hexec
                  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
                      _ _ "val" "sigOff" _ (by decide) hexec)
                hexec
            · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
                _ _ "sigOff" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "pkAdrs" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
          _ _ "sigOff" _ _ hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
          "i" "sigOff" _ _ _ _ (by decide)
          (by
            intro s s'' stmt hmem hexec
            simp only [c12WotsPkCopyBody, List.mem_cons, List.not_mem_nil,
              or_false] at hmem
            subst hmem
            exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
              _ _ "sigOff" _ _ hexec)
          hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "wotsPk" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "authOff" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "authPtr" "sigOff" _ (by decide) hexec
      · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
          _ _ "xmssBase" "sigOff" _ (by decide) hexec)
    (execC12LayerBodyBeforeXmssNode st)

def c12LayerStateAfterXmssLoop (st : RuntimeState) : RuntimeState :=
  SphincsMinusVerifiers.ClimbLoop.foldLoop "h" c12XmssStep
    { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
    0 (wordNormalize 4)

theorem c12XmssStep_eq_stepMerkle (st : RuntimeState) :
    c12XmssStep st =
      SphincsMinusVerifiers.ClimbKit.stepMerkle
        "merkleNode" "mIdx" "xmssBase" "authPtr" st := by
  unfold c12XmssStep SphincsMinusVerifiers.ClimbKit.stepMerkle
  rw [show c12XmssBody =
      SphincsMinusVerifiers.ClimbKit.merkleClimbBody
        "merkleNode" "mIdx" "xmssBase" "authPtr" by rfl]
  rfl

theorem c12LayerStateAfterXmssLoop_eq_merkleFold (st : RuntimeState) :
    c12LayerStateAfterXmssLoop st =
      SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
        (SphincsMinusVerifiers.ClimbKit.stepMerkle
          "merkleNode" "mIdx" "xmssBase" "authPtr")
        { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
        0 (wordNormalize 4) := by
  unfold c12LayerStateAfterXmssLoop
  congr

set_option maxHeartbeats 1200000 in
/-- One C12 XMSS climb step preserves the public-seed scratch cell for loop
states whose Merkle height `"h"` has just been bound by the loop adapter. -/
theorem c12XmssStep_preserves_memory_zero_bound (s : RuntimeState) (idx : Nat) :
    ((c12XmssStep { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let n : Nat := lookupValue stH.bindings "mIdx" % 2 ^ 256
  let sval : Nat := (Nat.land n 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  have hsvalt : sval < 2 ^ 256 := by
    show (Nat.land n 1) <<< 5 < 2 ^ 256
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  obtain ⟨vsib, h1⟩ : ∃ v, evalExpr [] stH
      (.bitAnd (.calldataload (.add (.localVar "authPtr")
        (.shl (.literal 4) (.localVar "h"))))
        (.literal SphincsMinusVerifiers.ClimbKit.N_MASK)) = some v := ⟨_, rfl⟩
  obtain ⟨vpar, h2⟩ : ∃ v,
      evalExpr [] { stH with bindings := bindValue stH.bindings "sibling" vsib }
        (.shr (.literal 1) (.localVar "mIdx")) = some v := ⟨_, rfl⟩
  obtain ⟨vadr, h3⟩ : ∃ v, evalExpr []
      { stH with bindings :=
        bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.bitOr (.localVar "xmssBase")
        (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
          (.localVar "parentIdx"))) = some v := ⟨_, rfl⟩
  let vnode : Nat :=
    lookupValue (bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
      "parentIdx" vpar) "s" sval) "merkleNode"
  let vsib2 : Nat :=
    lookupValue (bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
      "parentIdx" vpar) "s" sval) "sibling"
  have hmIdxH4 :
      lookupValue (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar) "mIdx"
        = lookupValue stH.bindings "mIdx" := by
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        (bindValue stH.bindings "sibling" vsib) "parentIdx" "mIdx" vpar (by decide),
      SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        stH.bindings "sibling" "mIdx" vsib (by decide)]
  have hbitand : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.bitAnd (.localVar "mIdx") (.literal 1)) = some (Nat.land n 1) := by
    have hbase := SphincsMinusVerifiers.SegmentS4ForsDataObligations.evalExpr_bitAnd_literal_modself
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.localVar "mIdx")
      (lookupValue (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar) "mIdx")
      1 rfl (by decide)
    rw [hmIdxH4] at hbase
    exact hbase
  have h4 : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval := by
    have hlit5 : evalExpr []
        { stH with
          world := { stH.world with memory :=
            SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
          bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
        (.literal 5) = some 5 := by
      show some (wordNormalize 5) = some 5
      rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
        Nat.mod_eq_of_lt (by decide)]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))
      5 (Nat.land n 1) hlit5 hbitand (by decide)
      (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) hsvalt
  have hs5 : lookupValue
      (bindValue (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar) "s" sval) "s"
      = sval :=
    SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self _ "s" sval
  have h5off : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      (.bitXor (.literal 0x40) (.localVar "s")) = some o5 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      0x40 sval hs5 (by decide) hsvalt
  have h5val : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      (.localVar "merkleNode") = some vnode := rfl
  have h6off : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate (SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 vnode },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      (.bitXor (.literal 0x60) (.localVar "s")) = some o6 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate (SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 vnode },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate (SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 vnode },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      (.localVar "sibling") = some vsib2 := rfl
  have hpar : n % 2 = 0 ∨ n % 2 = 1 := by
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  have hparOff : (n % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (n % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even n hzero
      have ho5 : o5 = 0x40 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x40
        exact ho.1
      have ho6 : o6 = 0x60 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x60
        exact ho.2
      exact ⟨hzero, ho5, ho6⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd n hone
      have ho5 : o5 = 0x60 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x60
        exact ho.1
      have ho6 : o6 = 0x40 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x40
        exact ho.2
      exact ⟨hone, ho5, ho6⟩
  show ((SphincsMinusVerifiers.ClimbKit.stepMerkle "merkleNode" "mIdx" "xmssBase" "authPtr"
      stH).world.memory 0).val = (stH.world.memory 0).val
  rw [← c12XmssStep_eq_stepMerkle stH]
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_mem_zero_val_of_parity
    "merkleNode" "mIdx" "xmssBase" "authPtr" stH
    vsib vpar vadr sval o5 vnode o6 vsib2 n hparOff h1 h2 h3 h4 h5off h5val h6off h6val

/-- The four-step C12 XMSS loop preserves the public-seed scratch cell. -/
theorem c12LayerStateAfterXmssLoop_preserves_memory_zero (st : RuntimeState) :
    ((c12LayerStateAfterXmssLoop st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  unfold c12LayerStateAfterXmssLoop
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_memory_val_bound
    "h" c12XmssStep 0x00 c12XmssStep_preserves_memory_zero_bound
    { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
    0 (wordNormalize 4)]

theorem execC12LayerXmssLoop (st : RuntimeState) :
    execStmt [] st (.forEach "h" (u 4) c12XmssBody) =
      .continue (c12LayerStateAfterXmssLoop st) := by
  unfold c12LayerStateAfterXmssLoop
  exact execStmt_forEach_of_step "h" (u 4) c12XmssBody st (wordNormalize 4)
    c12XmssStep rfl execC12XmssBody

def c12LayerBodyAfterCurrentNodeAssign : List Stmt := [
  .assignVar "currentNode" (v "merkleNode"),
  .assignVar "sigOff" (addE (v "authOff") (u 64)),
  .assignVar "curLeaf" (andE (v "curTree") (u 0xF)),
  .assignVar "curTree" (shrE (u 4) (v "curTree"))
]

theorem c12LayerBody_eq_beforeCurrentNode_append_after :
    c12LayerBody = c12LayerBodyBeforeCurrentNode ++ c12LayerBodyAfterCurrentNodeAssign := rfl

def c12LayerStateBeforeCurrentNode (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12LayerBodyBeforeCurrentNode with
  | .continue s' => s'
  | _ => st

theorem execC12LayerBodyBeforeCurrentNode (st : RuntimeState) :
    execStmtList [] st c12LayerBodyBeforeCurrentNode =
      .continue (c12LayerStateBeforeCurrentNode st) := by
  unfold c12LayerStateBeforeCurrentNode c12LayerBodyBeforeCurrentNode mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "wotsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 42) c12WotsMessageBody _ (wordNormalize 42)
      c12WotsMessageStep rfl execC12WotsMessageBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "csumShifted" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "j" (u 3) c12WotsChecksumBody _ (wordNormalize 3)
      c12WotsChecksumStep rfl execC12WotsChecksumBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "i" (u 45) c12WotsPkCopyBody _ (wordNormalize 45)
      c12WotsPkCopyStep rfl execC12WotsPkCopyBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "h" (u 4) c12XmssBody _ (wordNormalize 4)
      c12XmssStep rfl execC12XmssBody)]
  rfl

theorem c12LayerStateBeforeCurrentNode_eq_afterXmssLoop
    (st : RuntimeState) :
    c12LayerStateBeforeCurrentNode st =
      c12LayerStateAfterXmssLoop (c12LayerStateBeforeXmssLoop st) := by
  unfold c12LayerStateBeforeCurrentNode
  rw [c12LayerBodyBeforeCurrentNode_eq_beforeXmssLoop_append_xmss]
  rw [execStmtList_append_continue _ _ _ _
    (execC12LayerBodyBeforeXmssLoop st)]
  rw [execStmtList_cons_continue _ _ _ _
    (execC12LayerXmssLoop (c12LayerStateBeforeXmssLoop st))]
  rfl

theorem c12LayerStateBeforeCurrentNode_merkleNode_eq_afterXmssLoop
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeCurrentNode st).bindings "merkleNode" =
      lookupValue
        (c12LayerStateAfterXmssLoop (c12LayerStateBeforeXmssLoop st)).bindings
        "merkleNode" := by
  rw [c12LayerStateBeforeCurrentNode_eq_afterXmssLoop]

/-- The WOTS prefix plus XMSS loop preserves the public-seed scratch cell up to
the final current-node assignment tail. -/
theorem c12LayerStateBeforeCurrentNode_preserves_memory_zero
    (st : RuntimeState) :
    ((c12LayerStateBeforeCurrentNode st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rw [c12LayerStateBeforeCurrentNode_eq_afterXmssLoop]
  rw [c12LayerStateAfterXmssLoop_preserves_memory_zero]
  exact c12LayerStateBeforeXmssLoop_preserves_memory_zero st

/-- The folded XMSS loop and the final pre-XMSS setup bindings preserve the
`"authOff"` value computed before the XMSS loop. -/
theorem c12LayerStateBeforeCurrentNode_authOff_eq_beforeXmssNode_authOff
    (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeCurrentNode st).bindings "authOff" =
      lookupValue (c12LayerStateBeforeXmssNode st).bindings "authOff" := by
  rw [c12LayerStateBeforeCurrentNode_eq_afterXmssLoop]
  unfold c12LayerStateAfterXmssLoop
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "h" "authOff" c12XmssStep (by decide)
    (fun s => c12XmssStep_preserves_authOff s)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "h" "authOff" _ (by decide)]
  rw [c12LayerStateBeforeXmssLoop_authOff_eq_beforeXmssNode_authOff]

/-- One C12 layer assigns `"currentNode"` from the `"merkleNode"` computed by
the WOTS/XMSS body prefix. -/
theorem c12LayerStep_currentNode_eq_beforeCurrentNode_merkleNode
    (st : RuntimeState) :
    lookupValue (c12LayerStep st).bindings "currentNode" =
      lookupValue (c12LayerStateBeforeCurrentNode st).bindings "merkleNode" := by
  unfold c12LayerStep
  rw [c12LayerBody_eq_beforeCurrentNode_append_after]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeCurrentNode st)]
  unfold c12LayerBodyAfterCurrentNodeAssign
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "sigOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curTree" _ _ rfl)]
  change
    lookupValue
      (bindValue
        (bindValue
          (bindValue
            (bindValue (c12LayerStateBeforeCurrentNode st).bindings "currentNode"
              (lookupValue (c12LayerStateBeforeCurrentNode st).bindings "merkleNode"))
            "sigOff" _)
          "curLeaf" _)
        "curTree" _)
      "currentNode" =
    lookupValue (c12LayerStateBeforeCurrentNode st).bindings "merkleNode"
  rw [MemoryKit.lookupValue_bindValue_ne _ "curTree" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "curLeaf" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "sigOff" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]

/-- One complete C12 layer preserves the public-seed scratch cell. -/
theorem c12LayerStep_preserves_memory_zero (st : RuntimeState) :
    ((c12LayerStep st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  have hExecTail :
      execStmtList [] (c12LayerStateBeforeCurrentNode st)
          c12LayerBodyAfterCurrentNodeAssign =
        .continue (c12LayerStep st) := by
    unfold c12LayerStep
    rw [c12LayerBody_eq_beforeCurrentNode_append_after]
    rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeCurrentNode st)]
    unfold c12LayerBodyAfterCurrentNodeAssign
    rw [execStmtList_cons_continue _ _ _ _
      (assignVar_continue _ "currentNode" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _
      (assignVar_continue _ "sigOff" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _
      (assignVar_continue _ "curLeaf" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _
      (assignVar_continue _ "curTree" _ _ rfl)]
    rfl
  have hTail :
      ((c12LayerStep st).world.memory 0x00).val =
        ((c12LayerStateBeforeCurrentNode st).world.memory 0x00).val := by
    refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
      0x00 c12LayerBodyAfterCurrentNodeAssign
      (c12LayerStateBeforeCurrentNode st) (c12LayerStep st) ?_ hExecTail
    intro s s'' stmt hmem hexec
    simp only [c12LayerBodyAfterCurrentNodeAssign, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;>
      exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
        _ _ 0x00 _ _ hexec
  rw [hTail]
  exact c12LayerStateBeforeCurrentNode_preserves_memory_zero st

/-- One C12 layer's final tail assigns `"sigOff"` to `"authOff" + 64`, using
the `"authOff"` value established by the WOTS/XMSS body prefix. -/
theorem c12LayerStep_sigOff_eq_beforeCurrentNode_authOff
    (st : RuntimeState) :
    lookupValue (c12LayerStep st).bindings "sigOff" =
      (Verity.Core.Uint256.ofNat
          (lookupValue (c12LayerStateBeforeCurrentNode st).bindings "authOff") +
        Verity.Core.Uint256.ofNat (wordNormalize 64)).val := by
  unfold c12LayerStep
  rw [c12LayerBody_eq_beforeCurrentNode_append_after]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeCurrentNode st)]
  unfold c12LayerBodyAfterCurrentNodeAssign
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "sigOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curTree" _ _ rfl)]
  change
    lookupValue
      (bindValue
        (bindValue
          (bindValue
            (bindValue (c12LayerStateBeforeCurrentNode st).bindings "currentNode"
              (lookupValue (c12LayerStateBeforeCurrentNode st).bindings "merkleNode"))
            "sigOff" _)
          "curLeaf" _)
        "curTree" _)
      "sigOff" =
    (Verity.Core.Uint256.ofNat
        (lookupValue (c12LayerStateBeforeCurrentNode st).bindings "authOff") +
      Verity.Core.Uint256.ofNat (wordNormalize 64)).val
  rw [MemoryKit.lookupValue_bindValue_ne _ "curTree" "sigOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "curLeaf" "sigOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [MemoryKit.lookupValue_bindValue_ne _ "currentNode" "authOff" _ (by decide)]

/-- One C12 layer's final `"sigOff"` assignment can be read at the pre-XMSS-node
boundary: the XMSS loop preserves `"authOff"`, so `stepLayer` assigns
`"sigOff"` from the `"authOff"` established by the WOTS setup prefix. -/
theorem c12LayerStep_sigOff_eq_beforeXmssNode_authOff
    (st : RuntimeState) :
    lookupValue (c12LayerStep st).bindings "sigOff" =
      (Verity.Core.Uint256.ofNat
          (lookupValue (c12LayerStateBeforeXmssNode st).bindings "authOff") +
        Verity.Core.Uint256.ofNat (wordNormalize 64)).val := by
  rw [c12LayerStep_sigOff_eq_beforeCurrentNode_authOff]
  rw [c12LayerStateBeforeCurrentNode_authOff_eq_beforeXmssNode_authOff]

/-- The WOTS prefix and XMSS loop preserve `"curTree"` until the layer tail
updates it. -/
theorem c12LayerStateBeforeCurrentNode_curTree_eq (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeCurrentNode st).bindings "curTree" =
      lookupValue st.bindings "curTree" := by
  rw [c12LayerStateBeforeCurrentNode_eq_afterXmssLoop]
  unfold c12LayerStateAfterXmssLoop
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "h" "curTree" c12XmssStep (by decide) c12XmssStep_preserves_curTree]
  rw [MemoryKit.lookupValue_bindValue_ne _ "h" "curTree" _ (by decide)]
  rw [c12LayerStateBeforeXmssLoop_curTree_eq]

/-- One C12 layer assigns `"curLeaf"` from the low nibble of the incoming
`"curTree"` after the XMSS climb and current-node/sigOff tail. -/
theorem c12LayerStep_curLeaf_eq_of_curTree
    (st : RuntimeState) :
    lookupValue (c12LayerStep st).bindings "curLeaf" =
      (Verity.Core.Uint256.and
        (lookupValue st.bindings "curTree")
        (wordNormalize 0xF)).val := by
  unfold c12LayerStep
  rw [c12LayerBody_eq_beforeCurrentNode_append_after]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeCurrentNode st)]
  unfold c12LayerBodyAfterCurrentNodeAssign
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "sigOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curTree" _ _ rfl)]
  change
    lookupValue
      (bindValue
        (bindValue
          (bindValue
            (bindValue (c12LayerStateBeforeCurrentNode st).bindings "currentNode" _)
            "sigOff" _)
          "curLeaf"
            ((Verity.Core.Uint256.ofNat
              (lookupValue
                (bindValue
                  (bindValue (c12LayerStateBeforeCurrentNode st).bindings "currentNode" _)
                  "sigOff" _)
                "curTree")).and
              (Verity.Core.Uint256.ofNat (wordNormalize 0xF))).val)
        "curTree" _)
      "curLeaf" =
      (Verity.Core.Uint256.and
        (lookupValue st.bindings "curTree")
        (wordNormalize 0xF)).val
  rw [MemoryKit.lookupValue_bindValue_ne _ "curTree" "curLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "curTree" _ (by decide)]
  rw [c12LayerStateBeforeCurrentNode_curTree_eq]

/-- One C12 layer advances `"curTree"` by shifting out the low four bits after
they have been handed to `"curLeaf"`. -/
theorem c12LayerStep_curTree_eq_of_curTree
    (st : RuntimeState) :
    lookupValue (c12LayerStep st).bindings "curTree" =
      (Verity.Core.Uint256.shr
        (wordNormalize 4)
        (lookupValue st.bindings "curTree")).val := by
  unfold c12LayerStep
  rw [c12LayerBody_eq_beforeCurrentNode_append_after]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerBodyBeforeCurrentNode st)]
  unfold c12LayerBodyAfterCurrentNodeAssign
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "sigOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curTree" _ _ rfl)]
  change
    lookupValue
      (bindValue
        (bindValue
          (bindValue
            (bindValue (c12LayerStateBeforeCurrentNode st).bindings "currentNode" _)
            "sigOff" _)
          "curLeaf" _)
        "curTree"
          ((Verity.Core.Uint256.ofNat (wordNormalize 4)).shr
            (Verity.Core.Uint256.ofNat
              (lookupValue
                (bindValue
                  (bindValue
                    (bindValue (c12LayerStateBeforeCurrentNode st).bindings "currentNode" _)
                    "sigOff" _)
                  "curLeaf" _)
                "curTree"))).val)
      "curTree" =
      (Verity.Core.Uint256.shr
        (wordNormalize 4)
        (lookupValue st.bindings "curTree")).val
  rw [MemoryKit.lookupValue_bindValue_self]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "curTree" _ (by decide)]
  rw [c12LayerStateBeforeCurrentNode_curTree_eq]

/-- One C12 layer advances `"sigOff"` from the layer input through the WOTS and
XMSS-auth spans.  This exposes the recurrence without mentioning the intermediate
`"authOff"` binding. -/
theorem c12LayerStep_sigOff_eq_of_sigOff
    (st : RuntimeState) :
    lookupValue (c12LayerStep st).bindings "sigOff" =
      (Verity.Core.Uint256.ofNat
          ((Verity.Core.Uint256.ofNat (lookupValue st.bindings "sigOff") +
            Verity.Core.Uint256.ofNat (wordNormalize 720)).val) +
        Verity.Core.Uint256.ofNat (wordNormalize 64)).val := by
  rw [c12LayerStep_sigOff_eq_beforeXmssNode_authOff]
  rw [c12LayerStateBeforeXmssNode_authOff_eq_sigOff]

/-- The straight-line prefix through `"xmssBase"` does not rebind
`"sigBase"`. -/
theorem c12LayerStateBeforeXmssNode_sigBase_eq (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssNode st).bindings "sigBase" =
      lookupValue st.bindings "sigBase" := by
  unfold c12LayerStateBeforeXmssNode
  rw [c12LayerBodyBeforeXmssNode_eq_beforeAuthOff_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (execC12LayerBodyBeforeAuthOff st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforeAuthOff st) "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "xmssBase" _ _ rfl)]
  rw [lookup_match_execStmtList_nil]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "sigBase" _ (by decide)]
  rw [c12LayerStateBeforeAuthOff_sigBase_eq]

/-- The straight-line prefix before the XMSS loop does not rebind
`"sigBase"`. -/
theorem c12LayerStateBeforeXmssLoop_sigBase_eq (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeXmssLoop st).bindings "sigBase" =
      lookupValue st.bindings "sigBase" := by
  unfold c12LayerStateBeforeXmssLoop
  rw [c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (execC12LayerBodyBeforeXmssNode st)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (c12LayerStateBeforeXmssNode st) "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [lookup_match_execStmtList_nil]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "sigBase" _ (by decide)]
  rw [c12LayerStateBeforeXmssNode_sigBase_eq]

/-- The layer prefix through the XMSS loop does not rebind `"sigBase"`. -/
theorem c12LayerStateBeforeCurrentNode_sigBase_eq (st : RuntimeState) :
    lookupValue (c12LayerStateBeforeCurrentNode st).bindings "sigBase" =
      lookupValue st.bindings "sigBase" := by
  rw [c12LayerStateBeforeCurrentNode_eq_afterXmssLoop]
  unfold c12LayerStateAfterXmssLoop
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "h" "sigBase" c12XmssStep (by decide) c12XmssStep_preserves_sigBase]
  rw [MemoryKit.lookupValue_bindValue_ne _ "h" "sigBase" _ (by decide)]
  rw [c12LayerStateBeforeXmssLoop_sigBase_eq]

/-- One C12 hypertree layer iteration preserves `"sigBase"`. -/
theorem c12LayerStep_preserves_sigBase (st : RuntimeState) :
    lookupValue (c12LayerStep st).bindings "sigBase" =
      lookupValue st.bindings "sigBase" := by
  unfold c12LayerStep
  rw [c12LayerBody_eq_beforeCurrentNode_append_after]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (execC12LayerBodyBeforeCurrentNode st)]
  unfold c12LayerBodyAfterCurrentNodeAssign
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue (c12LayerStateBeforeCurrentNode st)
      "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "sigOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue _ "curTree" _ _ rfl)]
  rw [lookup_match_execStmtList_nil]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "sigBase" _ (by decide)]
  rw [c12LayerStateBeforeCurrentNode_sigBase_eq]

def c12LayerStmt : Stmt :=
  .forEach "layer" (u 5) c12LayerBody

theorem c12LayerLoopSegment_eq_slice :
    [c12LayerStmt] = C12SegmentForsCompress.c12AfterForsCompress.take 1 := rfl

def c12AfterLayerLoop : List Stmt :=
  C12SegmentForsCompress.c12AfterForsCompress.drop 1

theorem c12AfterForsCompress_eq :
    C12SegmentForsCompress.c12AfterForsCompress =
      [c12LayerStmt] ++ c12AfterLayerLoop := rfl

def c12StepLayerLoop (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st [c12LayerStmt] with
  | .continue s' => s'
  | _ => st

theorem execC12LayerLoop (st : RuntimeState) :
    execStmtList [] st [c12LayerStmt] = .continue (c12StepLayerLoop st) := by
  unfold c12StepLayerLoop c12LayerStmt
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "layer" (u 5) c12LayerBody st (wordNormalize 5)
      c12LayerStep rfl execC12LayerBody)]
  rfl

/-- The five-layer C12 WOTS/XMSS loop preserves `"sigBase"`. -/
theorem c12StepLayerLoop_preserves_sigBase (st : RuntimeState) :
    lookupValue (c12StepLayerLoop st).bindings "sigBase" =
      lookupValue st.bindings "sigBase" := by
  unfold c12StepLayerLoop c12LayerStmt
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "layer" (u 5) c12LayerBody st (wordNormalize 5)
      c12LayerStep rfl execC12LayerBody)]
  rw [lookup_match_execStmtList_nil]
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "layer" "sigBase" c12LayerStep (by decide) c12LayerStep_preserves_sigBase]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigBase" _ (by decide)]

theorem c12AfterForsCompress_observed_eq_after_layer_loop
    (st : RuntimeState) :
    observeStmtResultBool
        (execStmtList [] st C12SegmentForsCompress.c12AfterForsCompress)
      =
    observeStmtResultBool
        (execStmtList [] (c12StepLayerLoop st) c12AfterLayerLoop) := by
  rw [c12AfterForsCompress_eq]
  rw [execStmtList_append_continue _ _ _ _ (execC12LayerLoop st)]

private abbrev PreservesRoot (body : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ body → execStmt [] s stmt = .continue s'' →
    lookupValue s''.bindings "root" = lookupValue s.bindings "root"

private theorem c12WotsChainBody_preserves_root :
    PreservesRoot c12WotsChainBody := by
  intro s s'' stmt hmem hexec
  simp only [c12WotsChainBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "val" "root" _ (by decide) hexec

private theorem c12WotsMessageBody_preserves_root :
    PreservesRoot c12WotsMessageBody := by
  intro s s'' stmt hmem hexec
  simp only [c12WotsMessageBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "digit" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "csum" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "val" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "chainBase" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "steps" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "s" "root" _ _ _ _ (by decide) c12WotsChainBody_preserves_root hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "root" _ _ hexec

private theorem c12WotsChecksumBody_preserves_root :
    PreservesRoot c12WotsChecksumBody := by
  intro s s'' stmt hmem hexec
  simp only [c12WotsChecksumBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "digit" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "i" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "val" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "chainBase" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "steps" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "s" "root" _ _ _ _ (by decide) c12WotsChainBody_preserves_root hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "root" _ _ hexec

private theorem c12WotsPkCopyBody_preserves_root :
    PreservesRoot c12WotsPkCopyBody := by
  intro s s'' stmt hmem hexec
  simp only [c12WotsPkCopyBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
    _ _ "root" _ _ hexec

private theorem c12XmssBody_preserves_root : PreservesRoot c12XmssBody := by
  intro s s'' stmt hmem hexec
  simp only [c12XmssBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "sibling" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "parentIdx" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "s" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "merkleNode" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "mIdx" "root" _ (by decide) hexec

private theorem c12LayerBody_preserves_root : PreservesRoot c12LayerBody := by
  intro s s'' stmt hmem hexec
  simp only [c12LayerBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "wotsBase" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "wotsPtr" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "csum" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "i" "root" _ _ _ _ (by decide) c12WotsMessageBody_preserves_root hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "csumShifted" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "j" "root" _ _ _ _ (by decide) c12WotsChecksumBody_preserves_root hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "pkAdrs" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "i" "root" _ _ _ _ (by decide) c12WotsPkCopyBody_preserves_root hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "wotsPk" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "authOff" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "authPtr" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "xmssBase" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "merkleNode" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "mIdx" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "h" "root" _ _ _ _ (by decide) c12XmssBody_preserves_root hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "currentNode" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "sigOff" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "curLeaf" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "curTree" "root" _ (by decide) hexec

/-- One C12 hypertree layer iteration preserves `"root"`. -/
theorem c12LayerStep_preserves_root (st : RuntimeState) :
    lookupValue (c12LayerStep st).bindings "root" =
      lookupValue st.bindings "root" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "root" c12LayerBody st (c12LayerStep st)
    c12LayerBody_preserves_root
    (execC12LayerBody st)

/-- The five-layer C12 WOTS/XMSS loop preserves `"root"`. -/
theorem c12StepLayerLoop_preserves_root (st : RuntimeState) :
    lookupValue (c12StepLayerLoop st).bindings "root" =
      lookupValue st.bindings "root" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "root" [c12LayerStmt] st (c12StepLayerLoop st)
    (by
      intro s s'' stmt hmem hexec
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
        "layer" "root" _ _ _ _ (by decide) c12LayerBody_preserves_root hexec)
    (execC12LayerLoop st)

/-- The final C12 post-layer-loop state has the executable `"root"` binding
initialized from the public key root. -/
theorem c12FinalLayerLoop_root_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
        (c12StepLayerLoop
          (C12SegmentForsCompress.c12StepForsCompress
            (C12SegmentFors.c12StepFors
              (C12SegmentSeed.c12StepSeed
                (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
        "root" =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot := by
  rw [c12StepLayerLoop_preserves_root,
    C12SegmentForsCompress.c12StepForsCompress_preserves_root,
    C12SegmentFors.c12StepFors_preserves_root,
    C12SegmentSeed.c12StepSeed_root_mkC13State]

#print axioms execC12WotsChainBody
#print axioms c12WotsChainStep_preserves_memory_zero
#print axioms execC12WotsMessageBody
#print axioms execC12WotsChecksumBody
#print axioms execC12WotsPkCopyBody
#print axioms c12WotsPkCopyStep_preserves_memory_zero_bound
#print axioms c12WotsPkCopyStep_copies_chain_word
#print axioms c12WotsPkCopyStep_preserves_other_chain_word
#print axioms c12WotsPkCopyStep_preserves_memory_addr_of_ne
#print axioms c12WotsPkCopyLoop_copies_chain_word
#print axioms c12WotsPkCopyLoop_preserves_pkAdrs_slot
#print axioms c12WotsChainStep_val_eq
#print axioms c12WotsChainStep_preserves_lookup_of_ne_val
#print axioms c12WotsChain_foldLoop_val_eq
#print axioms chainHashC12_lt_two_pow
#print axioms c12WotsMessage_chainTail_mem_at_i
#print axioms c12WotsMessageStep_mem_at_i_via_prefix5
#print axioms c12WotsMessageLoop_mem_at_j_eq_of_suffix_preserves
#print axioms c12WotsChainBody_preserves_memory_addr_of_ne
#print axioms c12WotsMessagePrefix_preserves_memory_addr_of_ne
#print axioms c12WotsMessageBody_preserves_memory_addr_of_ne_bound
#print axioms c12WotsMessageStep_preserves_prior_message_cell
#print axioms c12WotsMessageLoop_mem_at_j_eq
#print axioms c12WotsChecksumPrefix_preserves_memory_addr_of_ne
#print axioms c12WotsChecksumBody_preserves_memory_addr_of_ne_bound
#print axioms c12WotsChecksumStep_preserves_prior_checksum_cell
#print axioms c12WotsChecksumStep_mem_at_j_eq
#print axioms c12WotsChecksumLoop_mem_at_j_eq
#print axioms evalExpr_sub_le_bounded
#print axioms evalExpr_subE_7_v_digit
#print axioms execStmt_letVar_steps_eq
#print axioms evalExpr_csum_add_subE_eq
#print axioms execStmt_assignVar_csum_eq
#print axioms evalExpr_chainBase_eq
#print axioms execStmt_letVar_chainBase_eq
#print axioms evalExpr_val_calldata_mask_eq
#print axioms execStmt_letVar_val_eq
#print axioms evalExpr_mul_bounded
#print axioms evalExpr_digit_eq
#print axioms and_seven_le_seven
#print axioms execStmt_letVar_digit_eq
#print axioms c12WotsMessageStep_mem_at_i_eq
#print axioms c12LayerStateBeforeXmssLoop_preserves_memory_zero
#print axioms c12XmssStep_preserves_memory_zero_bound
#print axioms c12LayerStateAfterXmssLoop_preserves_memory_zero
#print axioms c12LayerStateBeforeCurrentNode_preserves_memory_zero
#print axioms c12LayerStep_preserves_memory_zero
#print axioms execC12XmssBody
#print axioms execC12LayerBody
#print axioms execC12LayerLoop
#print axioms c12AfterForsCompress_observed_eq_after_layer_loop
#print axioms c12LayerStateBeforeXmssLoop_authOff_eq_beforeXmssNode_authOff
#print axioms c12LayerStateBeforeXmssLoop_authPtr_eq_beforeXmssNode_authPtr
#print axioms c12LayerStateBeforeXmssLoop_xmssBase_eq_beforeXmssNode_xmssBase
#print axioms c12LayerStateBeforeAuthOff_sigOff_eq
#print axioms c12LayerStateBeforeAuthOff_sigBase_eq
#print axioms c12LayerStateBeforeAuthOff_layer_eq
#print axioms c12LayerStateBeforeAuthOff_curTree_eq
#print axioms c12LayerStateBeforeXmssNode_wotsPk_eq_beforeAuthOff
#print axioms c12LayerStateBeforeXmssNode_xmssBase_eq_beforeAuthOff
#print axioms c12LayerStateBeforeXmssNode_curTree_eq
#print axioms c12LayerStateBeforeXmssLoop_curTree_eq
#print axioms c12LayerStateBeforeXmssNode_sigOff_eq
#print axioms c12LayerStateBeforeXmssNode_authOff_eq_sigOff
#print axioms c12LayerStateBeforeXmssNode_authPtr_eq_sigBase_sigOff
#print axioms c12XmssStep_preserves_authOff
#print axioms c12XmssStep_preserves_sigBase
#print axioms c12XmssStep_preserves_curTree
#print axioms c12LayerStateBeforeCurrentNode_authOff_eq_beforeXmssNode_authOff
#print axioms c12LayerStateBeforeCurrentNode_curTree_eq
#print axioms c12LayerStateBeforeXmssNode_sigBase_eq
#print axioms c12LayerStateBeforeXmssLoop_sigBase_eq
#print axioms c12LayerStateBeforeCurrentNode_sigBase_eq
#print axioms c12LayerStep_sigOff_eq_beforeCurrentNode_authOff
#print axioms c12LayerStep_sigOff_eq_beforeXmssNode_authOff
#print axioms c12LayerStep_curLeaf_eq_of_curTree
#print axioms c12LayerStep_curTree_eq_of_curTree
#print axioms c12LayerStep_sigOff_eq_of_sigOff
#print axioms c12LayerStep_preserves_root
#print axioms c12LayerStep_preserves_sigBase
#print axioms c12StepLayerLoop_preserves_root
#print axioms c12StepLayerLoop_preserves_sigBase
#print axioms c12FinalLayerLoop_root_mkC13State

end SphincsMinusVerifiers.C12SegmentWotsSetup
