import SphincsMinusVerifiers.Model
import SphincsMinusVerifiers.MemoryKit
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.StateFrame
import SphincsMinusVerifiers.ProofCore
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.SegmentS2R

namespace SphincsMinusVerifiers.C12SegmentSeed

open Compiler.CompilationModel (Stmt Expr)
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MemoryKit

private theorem c12_wordNormalize_of_lt {n : Nat} (h : n < 2 ^ 256) :
    wordNormalize n = n := by
  rw [wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt h

private theorem c12_wordOfHash16_lt (b : ByteArray) :
    SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 b < 2 ^ 256 := by
  unfold SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
  have h :
      SphincsMinusVerifierSpec.C13Concrete.baToNatBE b % (2 ^ 128) < 2 ^ 128 :=
    Nat.mod_lt _ (by positivity)
  calc (SphincsMinusVerifierSpec.C13Concrete.baToNatBE b % (2 ^ 128)) * (2 ^ 128)
      < (2 ^ 128) * (2 ^ 128) := Nat.mul_lt_mul_of_pos_right h (by positivity)
    _ = 2 ^ 256 := by rw [← pow_add]

private theorem c12_nat_land_low16 (x : Nat) :
    Nat.land x 0xFFFF = x % 2 ^ 16 := by
  change (x &&& (2 ^ 16 - 1)) = x % 2 ^ 16
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 16
  · have hmask : (2 ^ 16 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 16 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

private theorem c12_nat_land_low4 (x : Nat) :
    Nat.land x 0xF = x % 2 ^ 4 := by
  change (x &&& (2 ^ 4 - 1)) = x % 2 ^ 4
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 4
  · have hmask : (2 ^ 4 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 4 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def p (name : String) : Expr := .param name
private def andE (a b : Expr) : Expr := .bitAnd a b
private def cdload (off : Expr) : Expr := .calldataload off
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def shrE (a b : Expr) : Expr := .shr a b
private def shlE (a b : Expr) : Expr := .shl a b
private def orE (a b : Expr) : Expr := .bitOr a b

def c12SeedSetup : List Stmt := [
  .letVar "seed" (p "pkSeed"),
  .letVar "root" (p "pkRoot"),
  .letVar "sigBase" (v "sig_data_offset"),
  mstore 0x00 (v "seed"),
  mstore 0x20 (v "root"),
  mstore 0x40 (cdload (v "sigBase")),
  mstore 0x60 (p "message"),
  mstore 0x80 (u 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC),
  .letVar "dVal" (keccak 0x00 0xA0),
  .letVar "treeIdx" (andE (shrE (u 140) (v "dVal")) (u 0xFFFF)),
  .letVar "leafIdx" (andE (shrE (u 156) (v "dVal")) (u 0xF)),
  .letVar "forsBase" (orE (orE (shlE (u 160) (v "treeIdx")) (shlE (u 128) (u 3))) (shlE (u 96) (v "leafIdx"))),
  .letVar "forsOff" (u 32)
]

theorem c12SeedSetup_eq_slice :
    c12SeedSetup = c12VerifyBody.tail.take 13 := rfl

def c12AfterSeedSetup : List Stmt :=
  c12VerifyBody.tail.drop 13

theorem c12VerifyBody_tail_eq :
    c12VerifyBody.tail = c12SeedSetup ++ c12AfterSeedSetup := rfl

def c12StepSeed (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12SeedSetup with
  | .continue s' => s'
  | _ => st

theorem execC12SeedSetup (st : RuntimeState) :
    execStmtList [] st c12SeedSetup = .continue (c12StepSeed st) := by
  unfold c12StepSeed c12SeedSetup mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "seed" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "root" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "sigBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "dVal" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "leafIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "forsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "forsOff" _ _ rfl)]
  rfl

/-- C12 seed setup preserves the byte-facing selector/calldata frame. -/
theorem c12StepSeed_preserves_selector_calldata (st : RuntimeState) :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata st (c12StepSeed st) := by
  refine SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    c12SeedSetup st (c12StepSeed st) ?_ (execC12SeedSetup st)
  intro s s'' stmt hmem hexec
  simp only [c12SeedSetup, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "seed" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "root" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "sigBase" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "dVal" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "treeIdx" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "leafIdx" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "forsBase" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "forsOff" _ hexec

private def c12SeedRootPrefixState (st : RuntimeState) : RuntimeState :=
  let seedState : RuntimeState :=
    { st with
      bindings := bindValue st.bindings "seed" (lookupValue st.bindings "pkSeed") }
  { seedState with
    bindings :=
      bindValue seedState.bindings "root" (lookupValue seedState.bindings "pkRoot") }

/-- The first two C12 seed-setup statements bind `seed` and then `root`. -/
private theorem execC12SeedRootPrefix (st : RuntimeState) :
    execStmtList [] st (c12SeedSetup.take 2) =
      .continue (c12SeedRootPrefixState st) := by
  rw [show c12SeedSetup.take 2 =
    [(.letVar "seed" (.param "pkSeed") : Stmt), .letVar "root" (.param "pkRoot")] by
      rfl]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue st "seed" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue _ "root" _ _ rfl)]
  rfl

private theorem c12SeedSetupTail_preserves_root (st s' : RuntimeState)
    (hExec : execStmtList [] st (c12SeedSetup.drop 2) = .continue s') :
    lookupValue s'.bindings "root" = lookupValue st.bindings "root" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup "root" _ _ _ ?_ hExec
  intro s s'' stmt hmem hexec
  change stmt ∈ [
    .letVar "sigBase" (v "sig_data_offset"),
    mstore 0x00 (v "seed"),
    mstore 0x20 (v "root"),
    mstore 0x40 (cdload (v "sigBase")),
    mstore 0x60 (p "message"),
    mstore 0x80 (u 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC),
    .letVar "dVal" (keccak 0x00 0xA0),
    .letVar "treeIdx" (andE (shrE (u 140) (v "dVal")) (u 0xFFFF)),
    .letVar "leafIdx" (andE (shrE (u 156) (v "dVal")) (u 0xF)),
    .letVar "forsBase" (orE (orE (shlE (u 160) (v "treeIdx")) (shlE (u 128) (u 3)))
      (shlE (u 96) (v "leafIdx"))),
    .letVar "forsOff" (u 32)] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "sigBase" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "dVal" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "treeIdx" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "leafIdx" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsBase" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsOff" "root" _ (by decide) hexec

/-- C12 seed setup initializes the executable `"root"` binding from `pkRoot`. -/
theorem c12StepSeed_root_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
      (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings
      "root" =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot := by
  let prefixState :=
    c12SeedRootPrefixState (MkC13State.mkC13State pkSeed pkRoot message sig)
  have hPrefixRoot :
      lookupValue prefixState.bindings "root" =
        lookupValue (MkC13State.mkC13State pkSeed pkRoot message sig).bindings "pkRoot" := by
    dsimp [prefixState, c12SeedRootPrefixState]
    rw [MemoryKit.lookupValue_bindValue_self,
      MemoryKit.lookupValue_bindValue_ne _ "seed" "pkRoot" _ (by decide)]
  have hPrefixExec :
      execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig)
        (c12SeedSetup.take 2) = .continue prefixState := by
    exact execC12SeedRootPrefix (MkC13State.mkC13State pkSeed pkRoot message sig)
  have hTailExec :
      execStmtList [] prefixState (c12SeedSetup.drop 2) =
        .continue (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)) := by
    have hAll := execC12SeedSetup (MkC13State.mkC13State pkSeed pkRoot message sig)
    rw [show c12SeedSetup = c12SeedSetup.take 2 ++ c12SeedSetup.drop 2 by simp] at hAll
    rw [MemoryKit.execStmtList_append_continue _ _ _ _ hPrefixExec] at hAll
    exact hAll
  rw [c12SeedSetupTail_preserves_root prefixState
    (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)) hTailExec,
    hPrefixRoot]
  rfl

/-- C12 seed setup initializes the executable `"sigBase"` binding from the ABI
signature-data offset. -/
theorem c12StepSeed_sigBase_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
      (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings
      "sigBase" =
      MkC13State.sigDataOffset := by
  have hExec := execC12SeedSetup (MkC13State.mkC13State pkSeed pkRoot message sig)
  rw [show c12SeedSetup =
      [(.letVar "seed" (p "pkSeed") : Stmt),
       .letVar "root" (p "pkRoot"),
       .letVar "sigBase" (v "sig_data_offset")] ++
        c12SeedSetup.drop 3 by rfl] at hExec
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (by
      rw [execStmtList_cons_continue _ _ _ _
        (execStmt_letVar_continue
          (MkC13State.mkC13State pkSeed pkRoot message sig) "seed" _ _ rfl)]
      rw [execStmtList_cons_continue _ _ _ _
        (execStmt_letVar_continue _ "root" _ _ rfl)]
      rw [execStmtList_cons_continue _ _ _ _
        (execStmt_letVar_continue _ "sigBase" _ _ rfl)]
      rfl)] at hExec
  have hTail :
      lookupValue
          (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings
          "sigBase" =
        lookupValue
          (bindValue
            (bindValue
              (bindValue
                (MkC13State.mkC13State pkSeed pkRoot message sig).bindings
                "seed"
                (lookupValue
                  (MkC13State.mkC13State pkSeed pkRoot message sig).bindings
                  "pkSeed"))
              "root"
              (lookupValue
                (bindValue
                  (MkC13State.mkC13State pkSeed pkRoot message sig).bindings
                  "seed"
                  (lookupValue
                    (MkC13State.mkC13State pkSeed pkRoot message sig).bindings
                    "pkSeed"))
                "pkRoot"))
            "sigBase"
            (lookupValue
              (bindValue
                (bindValue
                  (MkC13State.mkC13State pkSeed pkRoot message sig).bindings
                  "seed"
                  (lookupValue
                    (MkC13State.mkC13State pkSeed pkRoot message sig).bindings
                    "pkSeed"))
                "root"
                (lookupValue
                  (bindValue
                    (MkC13State.mkC13State pkSeed pkRoot message sig).bindings
                    "seed"
                    (lookupValue
                      (MkC13State.mkC13State pkSeed pkRoot message sig).bindings
                      "pkSeed"))
                  "pkRoot"))
              "sig_data_offset"))
          "sigBase" := by
    exact BindingFrame.execStmtList_preserves_lookup "sigBase" (c12SeedSetup.drop 3) _
      (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig))
      (by
        intro s s'' stmt hmem hexec
        change stmt ∈ [
          mstore 0x00 (v "seed"),
          mstore 0x20 (v "root"),
          mstore 0x40 (cdload (v "sigBase")),
          mstore 0x60 (p "message"),
          mstore 0x80 (u 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC),
          .letVar "dVal" (keccak 0x00 0xA0),
          .letVar "treeIdx" (andE (shrE (u 140) (v "dVal")) (u 0xFFFF)),
          .letVar "leafIdx" (andE (shrE (u 156) (v "dVal")) (u 0xF)),
          .letVar "forsBase" (orE (orE (shlE (u 160) (v "treeIdx")) (shlE (u 128) (u 3)))
            (shlE (u 96) (v "leafIdx"))),
          .letVar "forsOff" (u 32)] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
        · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
        · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
        · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
        · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
        · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "dVal" "sigBase" _ (by decide) hexec
        · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "treeIdx" "sigBase" _ (by decide) hexec
        · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "leafIdx" "sigBase" _ (by decide) hexec
        · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsBase" "sigBase" _ (by decide) hexec
        · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsOff" "sigBase" _ (by decide) hexec)
      hExec
  rw [hTail]
  rw [MemoryKit.lookupValue_bindValue_self]
  rfl

private theorem c12SeedSetupAfterSeedStore_preserves_memory_zero (st s' : RuntimeState)
    (hExec : execStmtList [] st (c12SeedSetup.drop 4) = .continue s') :
    (s'.world.memory 0x00).val = (st.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 _ _ _ ?_ hExec
  intro s s'' stmt hmem hexec
  change stmt ∈ [
    mstore 0x20 (v "root"),
    mstore 0x40 (cdload (v "sigBase")),
    mstore 0x60 (p "message"),
    mstore 0x80 (u 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC),
    .letVar "dVal" (keccak 0x00 0xA0),
    .letVar "treeIdx" (andE (shrE (u 140) (v "dVal")) (u 0xFFFF)),
    .letVar "leafIdx" (andE (shrE (u 156) (v "dVal")) (u 0xF)),
    .letVar "forsBase" (orE (orE (shlE (u 160) (v "treeIdx")) (shlE (u 128) (u 3)))
      (shlE (u 96) (v "leafIdx"))),
    .letVar "forsOff" (u 32)] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ 0x00 _ _ (by
        intro ro rv hoff hval
        change evalExpr [] s (.literal 0x20) = some ro at hoff
        have hlit : evalExpr [] s (.literal 0x20) = some 0x20 := rfl
        rw [hlit] at hoff
        have hro : ro = 0x20 := Option.some.inj hoff.symm
        subst ro
        decide) hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ 0x00 _ _ (by
        intro ro rv hoff hval
        change evalExpr [] s (.literal 0x40) = some ro at hoff
        have hlit : evalExpr [] s (.literal 0x40) = some 0x40 := rfl
        rw [hlit] at hoff
        have hro : ro = 0x40 := Option.some.inj hoff.symm
        subst ro
        decide) hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ 0x00 _ _ (by
        intro ro rv hoff hval
        change evalExpr [] s (.literal 0x60) = some ro at hoff
        have hlit : evalExpr [] s (.literal 0x60) = some 0x60 := rfl
        rw [hlit] at hoff
        have hro : ro = 0x60 := Option.some.inj hoff.symm
        subst ro
        decide) hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ 0x00 _ _ (by
        intro ro rv hoff hval
        change evalExpr [] s (.literal 0x80) = some ro at hoff
        have hlit : evalExpr [] s (.literal 0x80) = some 0x80 := rfl
        rw [hlit] at hoff
        have hro : ro = 0x80 := Option.some.inj hoff.symm
        subst ro
        decide) hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "dVal" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "treeIdx" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "leafIdx" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "forsBase" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "forsOff" _ hexec

private def c12SeedMemoryPrefixState (st : RuntimeState) : RuntimeState :=
  let seedState : RuntimeState :=
    { st with bindings := bindValue st.bindings "seed" (lookupValue st.bindings "pkSeed") }
  let rootState : RuntimeState :=
    { seedState with
      bindings := bindValue seedState.bindings "root" (lookupValue seedState.bindings "pkRoot") }
  let sigBaseState : RuntimeState :=
    { rootState with
      bindings := bindValue rootState.bindings "sigBase" (lookupValue rootState.bindings "sig_data_offset") }
  { sigBaseState with
    world := { sigBaseState.world with
      memory := MemoryKit.memUpdate sigBaseState.world.memory 0x00
        (lookupValue sigBaseState.bindings "seed") } }

private theorem execC12SeedMemoryPrefix (st : RuntimeState) :
    execStmtList [] st (c12SeedSetup.take 4) =
      .continue (c12SeedMemoryPrefixState st) := by
  rw [show c12SeedSetup.take 4 =
    [ (.letVar "seed" (.param "pkSeed") : Stmt)
    , .letVar "root" (.param "pkRoot")
    , .letVar "sigBase" (.localVar "sig_data_offset")
    , .mstore (.literal 0x00) (.localVar "seed")
    ] by rfl]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue st "seed" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue _ "root" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue _ "sigBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- C12 seed setup initializes the executable public-seed scratch cell. -/
theorem c12StepSeed_memory_zero_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    ((c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).world.memory
      0x00).val =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed := by
  let prefixState :=
    c12SeedMemoryPrefixState (MkC13State.mkC13State pkSeed pkRoot message sig)
  have hPrefixExec :
      execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig)
        (c12SeedSetup.take 4) = .continue prefixState := by
    exact execC12SeedMemoryPrefix (MkC13State.mkC13State pkSeed pkRoot message sig)
  have hTailExec :
      execStmtList [] prefixState (c12SeedSetup.drop 4) =
        .continue (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)) := by
    have hAll := execC12SeedSetup (MkC13State.mkC13State pkSeed pkRoot message sig)
    rw [show c12SeedSetup = c12SeedSetup.take 4 ++ c12SeedSetup.drop 4 by simp] at hAll
    rw [MemoryKit.execStmtList_append_continue _ _ _ _ hPrefixExec] at hAll
    exact hAll
  rw [c12SeedSetupAfterSeedStore_preserves_memory_zero prefixState
    (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)) hTailExec]
  dsimp [prefixState, c12SeedMemoryPrefixState]
  rw [MemoryKit.lookupValue_bindValue_ne _ "sigBase" "seed" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "root" "seed" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [show lookupValue (MkC13State.mkC13State pkSeed pkRoot message sig).bindings "pkSeed" =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed from rfl]
  rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl]
  exact Nat.mod_eq_of_lt (c12_wordOfHash16_lt pkSeed)

private def c12HMsgDigestWord
    (pkSeed pkRoot message sig : ByteArray) : Nat :=
  SphincsMinusVerifierSpec.C13Concrete.keccakWords
    [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
    , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
    , SphincsMinusVerifierSpec.C13Concrete.baToNatBE (SphincsMinusVerifierSpec.C12Concrete.read32 sig 0) %
        SphincsMinusVerifierSpec.C13Concrete.wordMod
    , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
        SphincsMinusVerifierSpec.C13Concrete.wordMod
    , SphincsMinusVerifierSpec.C12Concrete.hMsgPad
    ]

/-- C12's full-word `R` read is the base-256 fold of the first 32 signature
bytes. -/
theorem c12_read32_eq_fold (sig : ByteArray) :
    SphincsMinusVerifierSpec.C13Concrete.baToNatBE
        (SphincsMinusVerifierSpec.C12Concrete.read32 sig 0)
      =
    (List.range 32).foldl
      (fun acc j => acc * 256 + ((sig[j]?.getD 0).toNat)) 0 := by
  unfold SphincsMinusVerifierSpec.C12Concrete.read32
  rw [SphincsMinusVerifiers.SegmentS2R.baToNatBE_toArray, List.foldl_map]
  rfl

/-- Local public-expression form of the first `bytesToWords` word. -/
theorem c12_bytesToWords_head_eq_fold (sig : ByteArray) :
    (MkC13State.bytesToWords sig).getD 0 0 =
    (List.range 32).foldl
      (fun acc j => acc * 256 + ((sig[j]?.getD (0 : UInt8)).toNat)) 0 := by
  unfold MkC13State.bytesToWords
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : 0 < (sig.size + 31) / 32
  · rw [List.getElem?_range h]
    simp only [Option.map_some, Option.getD_some, Nat.mul_zero, Nat.zero_add]
  · push_neg at h
    have hz : (sig.size + 31) / 32 = 0 := Nat.le_zero.mp h
    have hs : sig.size = 0 := by
      have hd := (Nat.div_eq_zero_iff (a := sig.size + 31) (b := 32)).mp hz
      omega
    rw [hz, List.range_zero]
    simp only [List.getElem?_nil, Option.map_none, Option.getD_none]
    symm
    have hb : ∀ j : Nat, (sig[j]?.getD (0 : UInt8)).toNat = 0 := by
      intro j
      rw [getElem?_neg]
      · rfl
      · omega
    clear h hz
    have : ∀ (init : Nat), init = 0 →
        (List.range 32).foldl
          (fun acc j => acc * 256 + ((sig[j]?.getD (0 : UInt8)).toNat)) init = 0 := by
      intro init hi
      induction (List.range 32) generalizing init with
      | nil => simpa using hi
      | cons a t ih => apply ih; simp [hb, hi]
    exact this 0 rfl

/-- The first frozen ABI signature word is exactly C12's full-word `R` read. -/
theorem c12_bytesToWords_head_eq_read32 (sig : ByteArray) :
    (MkC13State.bytesToWords sig).getD 0 0 =
      SphincsMinusVerifierSpec.C13Concrete.baToNatBE
        (SphincsMinusVerifierSpec.C12Concrete.read32 sig 0) := by
  rw [c12_bytesToWords_head_eq_fold, c12_read32_eq_fold]

/-- The frozen ABI read at `sig_data_offset` is the C12 full-word `R` value. -/
theorem c12_calldataload_R_word
    (pkSeed pkRoot message sig : ByteArray) :
    Compiler.Proofs.YulGeneration.calldataloadWord 0
      (MkC13State.headWords pkSeed pkRoot message sig.size ++
        MkC13State.bytesToWords sig)
      MkC13State.sigDataOffset =
    SphincsMinusVerifierSpec.C13Concrete.baToNatBE
      (SphincsMinusVerifierSpec.C12Concrete.read32 sig 0) %
        SphincsMinusVerifierSpec.C13Concrete.wordMod := by
  rw [show MkC13State.sigDataOffset = 164 by rfl]
  unfold Compiler.Proofs.YulGeneration.calldataloadWord
  norm_num
  rw [List.getElem?_append_right (by simp [MkC13State.headWords])]
  simp [MkC13State.headWords]
  rw [← List.getD_eq_getElem?_getD]
  rw [c12_bytesToWords_head_eq_read32]
  rfl

private def c12SeedPreDigestState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  let st0 := MkC13State.mkC13State pkSeed pkRoot message sig
  let st1 : RuntimeState :=
    { st0 with bindings := (bindValue st0.bindings "seed"
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)) }
  let st2 : RuntimeState :=
    { st1 with bindings := (bindValue st1.bindings "root"
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot)) }
  let st3 : RuntimeState :=
    { st2 with bindings := (bindValue st2.bindings "sigBase" MkC13State.sigDataOffset) }
  let st4 : RuntimeState :=
    { st3 with world := { st3.world with
        memory := MemoryKit.memUpdate st3.world.memory 0x00
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed) } }
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with
        memory := MemoryKit.memUpdate st4.world.memory 0x20
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot) } }
  let st6 : RuntimeState :=
    { st5 with world := { st5.world with
        memory := MemoryKit.memUpdate st5.world.memory 0x40
          (Compiler.Proofs.YulGeneration.calldataloadWord st5.selector st5.world.calldata
            (lookupValue st5.bindings "sigBase")) } }
  let st7 : RuntimeState :=
    { st6 with world := { st6.world with
        memory := MemoryKit.memUpdate st6.world.memory 0x60
          (SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
            SphincsMinusVerifierSpec.C13Concrete.wordMod) } }
  { st7 with world := { st7.world with
      memory := MemoryKit.memUpdate st7.world.memory 0x80
        SphincsMinusVerifierSpec.C12Concrete.hMsgPad } }

private theorem execC12SeedPreDigest_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig)
      (c12SeedSetup.take 8) =
        .continue (c12SeedPreDigestState pkSeed pkRoot message sig) := by
  rw [show c12SeedSetup.take 8 =
    [ (.letVar "seed" (.param "pkSeed") : Stmt)
    , .letVar "root" (.param "pkRoot")
    , .letVar "sigBase" (.localVar "sig_data_offset")
    , .mstore (.literal 0x00) (.localVar "seed")
    , .mstore (.literal 0x20) (.localVar "root")
    , .mstore (.literal 0x40) (.calldataload (.localVar "sigBase"))
    , .mstore (.literal 0x60) (.param "message")
    , .mstore (.literal 0x80)
        (.literal 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC)
    ] by rfl]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue
      (MkC13State.mkC13State pkSeed pkRoot message sig) "seed" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue _ "root" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue _ "sigBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

private theorem c12SeedPreDigest_memory_words
    (pkSeed pkRoot message sig : ByteArray) :
    ∀ i, (h : i < 5) →
      ((c12SeedPreDigestState pkSeed pkRoot message sig).world.memory
          (0x00 + 32 * i)).val =
        [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
        , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
        , SphincsMinusVerifierSpec.C13Concrete.baToNatBE
            (SphincsMinusVerifierSpec.C12Concrete.read32 sig 0) %
              SphincsMinusVerifierSpec.C13Concrete.wordMod
        , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
            SphincsMinusVerifierSpec.C13Concrete.wordMod
        , SphincsMinusVerifierSpec.C12Concrete.hMsgPad ][i] := by
  intro i h
  match i, h with
  | 0, _ =>
      simp [c12SeedPreDigestState, MemoryKit.memUpdate]
      rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl]
      exact Nat.mod_eq_of_lt (c12_wordOfHash16_lt pkSeed)
  | 1, _ =>
      simp [c12SeedPreDigestState, MemoryKit.memUpdate]
      rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl]
      exact Nat.mod_eq_of_lt (c12_wordOfHash16_lt pkRoot)
  | 2, _ =>
      simp [c12SeedPreDigestState, MemoryKit.memUpdate]
      rw [show Verity.Core.Uint256.modulus =
          SphincsMinusVerifierSpec.C13Concrete.wordMod from rfl]
      rw [show (MkC13State.mkC13State pkSeed pkRoot message sig).selector = 0 from rfl]
      rw [show (MkC13State.mkC13State pkSeed pkRoot message sig).world.calldata =
          MkC13State.headWords pkSeed pkRoot message sig.size ++
            MkC13State.bytesToWords sig from rfl]
      rw [c12_calldataload_R_word]
      rw [Nat.mod_mod]
  | 3, _ =>
      simp [c12SeedPreDigestState, MemoryKit.memUpdate]
      rw [show Verity.Core.Uint256.modulus =
          SphincsMinusVerifierSpec.C13Concrete.wordMod from rfl]
      rw [Nat.mod_mod]
  | 4, _ =>
      simp [c12SeedPreDigestState, MemoryKit.memUpdate,
        SphincsMinusVerifierSpec.C12Concrete.hMsgPad]
      rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl]
      exact Nat.mod_eq_of_lt (by norm_num)
  | n + 5, h => omega

private theorem c12SeedPreDigest_eval_dVal
    (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (c12SeedPreDigestState pkSeed pkRoot message sig)
      (.keccak256 (.literal 0x00) (.literal 0xA0)) =
        some (c12HMsgDigestWord pkSeed pkRoot message sig) := by
  unfold c12HMsgDigestWord
  refine SphincsMinusVerifiers.KeccakBridge.evalExpr_keccak256_eq_keccakWords
    (c12SeedPreDigestState pkSeed pkRoot message sig) 0x00 0xA0
    [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
    , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
    , SphincsMinusVerifierSpec.C13Concrete.baToNatBE
        (SphincsMinusVerifierSpec.C12Concrete.read32 sig 0) %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
    , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
        SphincsMinusVerifierSpec.C13Concrete.wordMod
    , SphincsMinusVerifierSpec.C12Concrete.hMsgPad ] ?_ ?_ ?_
  · rfl
  · rfl
  · exact c12SeedPreDigest_memory_words pkSeed pkRoot message sig

private def c12SeedDigestState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  { c12SeedPreDigestState pkSeed pkRoot message sig with
    bindings := bindValue
      (c12SeedPreDigestState pkSeed pkRoot message sig).bindings
      "dVal" (c12HMsgDigestWord pkSeed pkRoot message sig) }

private theorem c12HMsgDigestWord_lt
    (pkSeed pkRoot message sig : ByteArray) :
    c12HMsgDigestWord pkSeed pkRoot message sig < 2 ^ 256 := by
  unfold c12HMsgDigestWord
  have h := SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
    [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
    , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
    , SphincsMinusVerifierSpec.C13Concrete.baToNatBE
        (SphincsMinusVerifierSpec.C12Concrete.read32 sig 0) %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
    , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
        SphincsMinusVerifierSpec.C13Concrete.wordMod
    , SphincsMinusVerifierSpec.C12Concrete.hMsgPad ]
  rwa [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl] at h

private theorem c12SeedDigestState_eval_treeIdx
    (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (c12SeedDigestState pkSeed pkRoot message sig)
      (andE (shrE (u 140) (v "dVal")) (u 0xFFFF)) =
        some ((c12HMsgDigestWord pkSeed pkRoot message sig >>> 140) % (2 ^ 16)) := by
  have hd :
      evalExpr [] (c12SeedDigestState pkSeed pkRoot message sig) (v "dVal") =
        some (c12HMsgDigestWord pkSeed pkRoot message sig) := by
    change some (lookupValue (c12SeedDigestState pkSeed pkRoot message sig).bindings "dVal") =
      some (c12HMsgDigestWord pkSeed pkRoot message sig)
    simp [c12SeedDigestState]
  have hshr :
      evalExpr [] (c12SeedDigestState pkSeed pkRoot message sig)
        (shrE (u 140) (v "dVal")) =
        some (c12HMsgDigestWord pkSeed pkRoot message sig >>> 140) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      (c12SeedDigestState pkSeed pkRoot message sig) (u 140) (v "dVal")
      140 (c12HMsgDigestWord pkSeed pkRoot message sig)
      rfl hd (by decide) (c12HMsgDigestWord_lt pkSeed pkRoot message sig)
  have hshiftLt :
      c12HMsgDigestWord pkSeed pkRoot message sig >>> 140 < 2 ^ 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt
      (Nat.div_le_self (c12HMsgDigestWord pkSeed pkRoot message sig) (2 ^ 140))
      (c12HMsgDigestWord_lt pkSeed pkRoot message sig)
  have hand :
      evalExpr [] (c12SeedDigestState pkSeed pkRoot message sig)
        (andE (shrE (u 140) (v "dVal")) (u 0xFFFF)) =
        some (Nat.land (c12HMsgDigestWord pkSeed pkRoot message sig >>> 140) 0xFFFF) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
      (c12SeedDigestState pkSeed pkRoot message sig)
      (shrE (u 140) (v "dVal")) (c12HMsgDigestWord pkSeed pkRoot message sig >>> 140)
      0xFFFF hshr hshiftLt (by decide)
  rw [hand, c12_nat_land_low16]

private def c12SeedTreeState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  { c12SeedDigestState pkSeed pkRoot message sig with
    bindings := bindValue
      (c12SeedDigestState pkSeed pkRoot message sig).bindings
      "treeIdx" ((c12HMsgDigestWord pkSeed pkRoot message sig >>> 140) % (2 ^ 16)) }

private theorem c12SeedTreeState_eval_leafIdx
    (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (c12SeedTreeState pkSeed pkRoot message sig)
      (andE (shrE (u 156) (v "dVal")) (u 0xF)) =
        some ((c12HMsgDigestWord pkSeed pkRoot message sig >>> 156) % (2 ^ 4)) := by
  have hd :
      evalExpr [] (c12SeedTreeState pkSeed pkRoot message sig) (v "dVal") =
        some (c12HMsgDigestWord pkSeed pkRoot message sig) := by
    change some (lookupValue (c12SeedTreeState pkSeed pkRoot message sig).bindings "dVal") =
      some (c12HMsgDigestWord pkSeed pkRoot message sig)
    simp [c12SeedTreeState, c12SeedDigestState, MemoryKit.lookupValue_bindValue_ne]
  have hshr :
      evalExpr [] (c12SeedTreeState pkSeed pkRoot message sig)
        (shrE (u 156) (v "dVal")) =
        some (c12HMsgDigestWord pkSeed pkRoot message sig >>> 156) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      (c12SeedTreeState pkSeed pkRoot message sig) (u 156) (v "dVal")
      156 (c12HMsgDigestWord pkSeed pkRoot message sig)
      rfl hd (by decide) (c12HMsgDigestWord_lt pkSeed pkRoot message sig)
  have hshiftLt :
      c12HMsgDigestWord pkSeed pkRoot message sig >>> 156 < 2 ^ 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt
      (Nat.div_le_self (c12HMsgDigestWord pkSeed pkRoot message sig) (2 ^ 156))
      (c12HMsgDigestWord_lt pkSeed pkRoot message sig)
  have hand :
      evalExpr [] (c12SeedTreeState pkSeed pkRoot message sig)
        (andE (shrE (u 156) (v "dVal")) (u 0xF)) =
        some (Nat.land (c12HMsgDigestWord pkSeed pkRoot message sig >>> 156) 0xF) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
      (c12SeedTreeState pkSeed pkRoot message sig)
      (shrE (u 156) (v "dVal")) (c12HMsgDigestWord pkSeed pkRoot message sig >>> 156)
      0xF hshr hshiftLt (by decide)
  rw [hand, c12_nat_land_low4]

private def c12SeedLeafState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  { c12SeedTreeState pkSeed pkRoot message sig with
    bindings := bindValue
      (c12SeedTreeState pkSeed pkRoot message sig).bindings
      "leafIdx" ((c12HMsgDigestWord pkSeed pkRoot message sig >>> 156) % (2 ^ 4)) }

private theorem execC12SeedDigestPrefix_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig)
      (c12SeedSetup.take 9) =
        .continue (c12SeedDigestState pkSeed pkRoot message sig) := by
  rw [show c12SeedSetup.take 9 =
      c12SeedSetup.take 8 ++ [(.letVar "dVal" (keccak 0x00 0xA0) : Stmt)] by
    rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (execC12SeedPreDigest_mkC13State pkSeed pkRoot message sig)]
  change (match
      evalExpr [] (c12SeedPreDigestState pkSeed pkRoot message sig)
        (.keccak256 (.literal 0x00) (.literal 0xA0))
    with
    | some resolved =>
        StmtResult.continue
          { c12SeedPreDigestState pkSeed pkRoot message sig with
            bindings := bindValue
              (c12SeedPreDigestState pkSeed pkRoot message sig).bindings
              "dVal" resolved }
    | none => StmtResult.revert) =
    StmtResult.continue (c12SeedDigestState pkSeed pkRoot message sig)
  rw [c12SeedPreDigest_eval_dVal]
  unfold c12SeedDigestState
  rfl

private theorem c12SeedSetupTail_preserves_dVal (st s' : RuntimeState)
    (hExec : execStmtList [] st (c12SeedSetup.drop 9) = .continue s') :
    lookupValue s'.bindings "dVal" = lookupValue st.bindings "dVal" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "dVal" _ _ _ ?_ hExec
  intro s s'' stmt hmem hexec
  change stmt ∈ [
    .letVar "treeIdx" (andE (shrE (u 140) (v "dVal")) (u 0xFFFF)),
    .letVar "leafIdx" (andE (shrE (u 156) (v "dVal")) (u 0xF)),
    .letVar "forsBase" (orE (orE (shlE (u 160) (v "treeIdx")) (shlE (u 128) (u 3)))
      (shlE (u 96) (v "leafIdx"))),
    .letVar "forsOff" (u 32)] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "treeIdx" "dVal" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "leafIdx" "dVal" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsBase" "dVal" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsOff" "dVal" _ (by decide) hexec

/-- The executable C12 seed setup binds `"dVal"` to the same digest word used by
`C12Concrete.hMsgC12`. -/
theorem c12StepSeed_dVal_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
      (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings
      "dVal" =
    c12HMsgDigestWord pkSeed pkRoot message sig := by
  have hExec := execC12SeedSetup (MkC13State.mkC13State pkSeed pkRoot message sig)
  rw [show c12SeedSetup = c12SeedSetup.take 9 ++ c12SeedSetup.drop 9 by simp] at hExec
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (execC12SeedDigestPrefix_mkC13State pkSeed pkRoot message sig)] at hExec
  rw [c12SeedSetupTail_preserves_dVal
    (c12SeedDigestState pkSeed pkRoot message sig)
    (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)) hExec]
  simp [c12SeedDigestState]

/-- Public-facing form of `c12StepSeed_dVal_mkC13State`: under a successful C12
parse, the executable `"dVal"` binding is the explicit digest word used by
`C12Concrete.hMsgC12`. -/
theorem c12StepSeed_dVal_hMsgC12_words
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : SphincsMinusVerifierSpec.Signature)
    (hParse : SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12
        SphincsMinusVerifierSpec.c12 sig = some sigParsed) :
    lookupValue
      (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings
      "dVal" =
    SphincsMinusVerifierSpec.C13Concrete.keccakWords
      [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
      , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE sigParsed.R %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , SphincsMinusVerifierSpec.C12Concrete.hMsgPad ] := by
  rw [c12StepSeed_dVal_mkC13State]
  unfold c12HMsgDigestWord
  rw [SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12_R hParse]

private theorem execC12SeedTreePrefix_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig)
      (c12SeedSetup.take 10) =
        .continue (c12SeedTreeState pkSeed pkRoot message sig) := by
  rw [show c12SeedSetup.take 10 =
      c12SeedSetup.take 9 ++
        [(.letVar "treeIdx" (andE (shrE (u 140) (v "dVal")) (u 0xFFFF)) : Stmt)] by
    rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (execC12SeedDigestPrefix_mkC13State pkSeed pkRoot message sig)]
  change (match
      evalExpr [] (c12SeedDigestState pkSeed pkRoot message sig)
        (andE (shrE (u 140) (v "dVal")) (u 0xFFFF))
    with
    | some resolved =>
        StmtResult.continue
          { c12SeedDigestState pkSeed pkRoot message sig with
            bindings := bindValue
              (c12SeedDigestState pkSeed pkRoot message sig).bindings
              "treeIdx" resolved }
    | none => StmtResult.revert) =
    StmtResult.continue (c12SeedTreeState pkSeed pkRoot message sig)
  rw [c12SeedDigestState_eval_treeIdx]
  unfold c12SeedTreeState
  rfl

private theorem c12SeedSetupAfterTree_preserves_treeIdx (st s' : RuntimeState)
    (hExec : execStmtList [] st (c12SeedSetup.drop 10) = .continue s') :
    lookupValue s'.bindings "treeIdx" = lookupValue st.bindings "treeIdx" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "treeIdx" _ _ _ ?_ hExec
  intro s s'' stmt hmem hexec
  change stmt ∈ [
    .letVar "leafIdx" (andE (shrE (u 156) (v "dVal")) (u 0xF)),
    .letVar "forsBase" (orE (orE (shlE (u 160) (v "treeIdx")) (shlE (u 128) (u 3)))
      (shlE (u 96) (v "leafIdx"))),
    .letVar "forsOff" (u 32)] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "leafIdx" "treeIdx" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsBase" "treeIdx" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsOff" "treeIdx" _ (by decide) hexec

/-- The executable C12 seed setup's `"treeIdx"` binding is the high hypertree
index extracted from the C12 H_msg digest. -/
theorem c12StepSeed_treeIdx_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
      (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings
      "treeIdx" =
    (c12HMsgDigestWord pkSeed pkRoot message sig >>> 140) % (2 ^ 16) := by
  have hExec := execC12SeedSetup (MkC13State.mkC13State pkSeed pkRoot message sig)
  rw [show c12SeedSetup = c12SeedSetup.take 10 ++ c12SeedSetup.drop 10 by simp] at hExec
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (execC12SeedTreePrefix_mkC13State pkSeed pkRoot message sig)] at hExec
  rw [c12SeedSetupAfterTree_preserves_treeIdx
    (c12SeedTreeState pkSeed pkRoot message sig)
    (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)) hExec]
  simp [c12SeedTreeState]

private theorem execC12SeedLeafPrefix_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig)
      (c12SeedSetup.take 11) =
        .continue (c12SeedLeafState pkSeed pkRoot message sig) := by
  rw [show c12SeedSetup.take 11 =
      c12SeedSetup.take 10 ++
        [(.letVar "leafIdx" (andE (shrE (u 156) (v "dVal")) (u 0xF)) : Stmt)] by
    rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (execC12SeedTreePrefix_mkC13State pkSeed pkRoot message sig)]
  change (match
      evalExpr [] (c12SeedTreeState pkSeed pkRoot message sig)
        (andE (shrE (u 156) (v "dVal")) (u 0xF))
    with
    | some resolved =>
        StmtResult.continue
          { c12SeedTreeState pkSeed pkRoot message sig with
            bindings := bindValue
              (c12SeedTreeState pkSeed pkRoot message sig).bindings
              "leafIdx" resolved }
    | none => StmtResult.revert) =
    StmtResult.continue (c12SeedLeafState pkSeed pkRoot message sig)
  rw [c12SeedTreeState_eval_leafIdx]
  unfold c12SeedLeafState
  rfl

private theorem c12SeedSetupAfterLeaf_preserves_leafIdx (st s' : RuntimeState)
    (hExec : execStmtList [] st (c12SeedSetup.drop 11) = .continue s') :
    lookupValue s'.bindings "leafIdx" = lookupValue st.bindings "leafIdx" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "leafIdx" _ _ _ ?_ hExec
  intro s s'' stmt hmem hexec
  change stmt ∈ [
    .letVar "forsBase" (orE (orE (shlE (u 160) (v "treeIdx")) (shlE (u 128) (u 3)))
      (shlE (u 96) (v "leafIdx"))),
    .letVar "forsOff" (u 32)] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsBase" "leafIdx" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "forsOff" "leafIdx" _ (by decide) hexec

/-- The executable C12 seed setup's `"leafIdx"` binding is the low leaf nibble
extracted from the C12 H_msg digest. -/
theorem c12StepSeed_leafIdx_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
      (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings
      "leafIdx" =
    (c12HMsgDigestWord pkSeed pkRoot message sig >>> 156) % (2 ^ 4) := by
  have hExec := execC12SeedSetup (MkC13State.mkC13State pkSeed pkRoot message sig)
  rw [show c12SeedSetup = c12SeedSetup.take 11 ++ c12SeedSetup.drop 11 by simp] at hExec
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (execC12SeedLeafPrefix_mkC13State pkSeed pkRoot message sig)] at hExec
  rw [c12SeedSetupAfterLeaf_preserves_leafIdx
    (c12SeedLeafState pkSeed pkRoot message sig)
    (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)) hExec]
  simp [c12SeedLeafState]

/-- Public-facing form of `c12StepSeed_treeIdx_mkC13State`: under a successful
C12 parse, the executable `"treeIdx"` binding is the tree index extracted by
`C12Concrete.hMsgC12`. -/
theorem c12StepSeed_treeIdx_hMsgC12_words
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : SphincsMinusVerifierSpec.Signature)
    (hParse : SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12
        SphincsMinusVerifierSpec.c12 sig = some sigParsed) :
    lookupValue
      (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings
      "treeIdx" =
    (SphincsMinusVerifierSpec.C13Concrete.keccakWords
      [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
      , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE sigParsed.R %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , SphincsMinusVerifierSpec.C12Concrete.hMsgPad ] >>> 140) % (2 ^ 16) := by
  rw [c12StepSeed_treeIdx_mkC13State]
  unfold c12HMsgDigestWord
  rw [SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12_R hParse]

/-- Public-facing form of `c12StepSeed_leafIdx_mkC13State`: under a successful
C12 parse, the executable `"leafIdx"` binding is the leaf nibble extracted by
`C12Concrete.hMsgC12`. -/
theorem c12StepSeed_leafIdx_hMsgC12_words
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : SphincsMinusVerifierSpec.Signature)
    (hParse : SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12
        SphincsMinusVerifierSpec.c12 sig = some sigParsed) :
    lookupValue
      (c12StepSeed (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings
      "leafIdx" =
    (SphincsMinusVerifierSpec.C13Concrete.keccakWords
      [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
      , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE sigParsed.R %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , SphincsMinusVerifierSpec.C12Concrete.hMsgPad ] >>> 156) % (2 ^ 4) := by
  rw [c12StepSeed_leafIdx_mkC13State]
  unfold c12HMsgDigestWord
  rw [SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12_R hParse]

#print axioms c12StepSeed_sigBase_mkC13State
#print axioms c12StepSeed_memory_zero_mkC13State
#print axioms c12_read32_eq_fold
#print axioms c12_bytesToWords_head_eq_fold
#print axioms c12_bytesToWords_head_eq_read32
#print axioms c12_calldataload_R_word
#print axioms c12SeedPreDigest_eval_dVal
#print axioms c12StepSeed_dVal_mkC13State
#print axioms c12StepSeed_dVal_hMsgC12_words
#print axioms c12StepSeed_treeIdx_mkC13State
#print axioms c12StepSeed_leafIdx_mkC13State
#print axioms c12StepSeed_treeIdx_hMsgC12_words
#print axioms c12StepSeed_leafIdx_hMsgC12_words

end SphincsMinusVerifiers.C12SegmentSeed
