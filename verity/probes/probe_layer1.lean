/-
  Probe v2: discharge of the
  `c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer1`
  axiom (Proofs.lean:11607).  Layer-1 twin of the ok-path layer-0 probes.
  The entry scalar facts at `c13BeforeWotsPkLightState (c13SecondLayerGuardState …)`
  feed the verified closure `c13Layer1_copyFold43_wotsChainsEnd_cells_of_inputs`.

  The layer-1 `"currentNode"` fact (the heavy lemma `probe_current0Root`) is
  derived through the LAYER-0-ONLY residual
  `c13_ok_afterMerkle_initial_wotsPk_residual_layer0`, NOT through the layer-1
  afterMerkle residual (which itself depends on the axiom being discharged).
  When folding into Proofs.lean the discharged theorem must therefore MOVE
  after line 11812 (`c13_ok_afterMerkle_initial_wotsPk_residual_layer0`) and
  its consumers (11645+) reorder below it.

  Split into per-fact lemmas so each declaration gets a fresh heartbeat budget
  and any divergence is localized.
-/
import SphincsMinusVerifiers.Proofs

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

/-- Lightweight entry state world projection (bindings-only updates). -/
private theorem probe_light_world (ls : RuntimeState) :
    (c13BeforeWotsPkLightState ls).world = (SegmentLayer3.afterDigit ls).world := rfl

/-- Lightweight entry state bindings shape. -/
private theorem probe_light_bindings (ls : RuntimeState) :
    (c13BeforeWotsPkLightState ls).bindings =
      bindValue
        (bindValue (SegmentLayer3.afterDigit ls).bindings "wotsPtr"
          ((evalExpr [] (SegmentLayer3.afterDigit ls)
            (.add (.localVar "sigBase") (.localVar "sigOff"))).getD 0))
        "i" (wordNormalize 0) := rfl

/-- The two trailing `letVar`s of the pre-checksum prefix (`"d"`, `"digitSum"`)
preserve every other binding from the pre-digest cutpoint. -/
private theorem probe_beforeDigitLoop_lookup_eq_beforeDigest_of_ne
    (ls : RuntimeState) (key : String)
    (hneD : "d" ≠ key) (hneSum : "digitSum" ≠ key) :
    lookupValue (SegmentLayer3.beforeDigitLoop ls).bindings key =
      lookupValue (SegmentLayer3.beforeDigest ls).bindings key := by
  have h : execStmtList [] ls
      (SegmentLayer3.prefixBeforeDigest ++
        [ Compiler.CompilationModel.Stmt.letVar "d"
            (.keccak256 (.literal 0x00) (.literal 0x80))
        , Compiler.CompilationModel.Stmt.letVar "digitSum" (.literal 0) ]) =
      .continue (SegmentLayer3.beforeDigitLoop ls) :=
    SegmentLayer3.beforeDigitLoop_eq ls
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (SegmentLayer3.beforeDigest_eq ls)] at h
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "d" _ _ rfl)] at h
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "digitSum" _ _ rfl)] at h
  have hnil : ∀ (s : RuntimeState), execStmtList [] s [] = StmtResult.continue s :=
    fun _ => rfl
  rw [hnil] at h
  have he := StmtResult.continue.inj h
  rw [← he]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" key _ hneSum]
  rw [MemoryKit.lookupValue_bindValue_ne _ "d" key _ hneD]

/-- The pre-checksum prefix does not rebind `"sigOff"`. -/
private theorem probe_beforeDigitLoop_preserves_sigOff (ls : RuntimeState) :
    lookupValue (SegmentLayer3.beforeDigitLoop ls).bindings "sigOff" =
      lookupValue ls.bindings "sigOff" := by
  refine BindingFrame.execStmtList_preserves_lookup "sigOff"
    SegmentLayer3.prefixBeforeDigitLoop
    ls (SegmentLayer3.beforeDigitLoop ls) ?_ (SegmentLayer3.beforeDigitLoop_eq ls)
  intro s s'' stmt hmem hexec
  simp [SegmentLayer3.prefixBeforeDigitLoop] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "idxLeaf" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_assignVar_preserves_lookup _ _ "idxTree" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "wotsAdrs" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "countOff" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "count" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigOff" _ _ hexec
  · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigOff" _ _ hexec
  · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigOff" _ _ hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "d" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "digitSum" "sigOff" _ (by decide) hexec

set_option maxHeartbeats 2000000 in
/-- Seed cell at the layer-1 lightweight entry state. -/
private theorem probe_seed1 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    ((c13BeforeWotsPkLightState
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [probe_light_world]
  rw [SegmentLayer3.afterDigit_preserves_memory_zero]
  unfold c13SecondLayerGuardState
  rw [ClimbLoopGuarded.loopState_preserves_memory_val]
  exact c13FirstStepLayer_seed_slot_of_memory_zero pkSeed pkRoot message sig
    (by
      simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using
        c13FirstLayerStep_preserves_memory_zero_of_parse
          pkSeed pkRoot message sig sigParsed hParse)

set_option maxHeartbeats 2000000 in
/-- The layer-1 guard-state `"currentNode"` binding is the layer-0 spec root,
derived through the LAYER-0-ONLY afterMerkle WOTS-PK residual. -/
private theorem probe_current0Root (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot)
    (d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers specRoot) :
    lookupValue (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
        "currentNode" = C13Concrete.wordOfHash16 d.root0 := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hWotsPk0 :
      C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13_ok_afterMerkle_initial_wotsPk_residual_layer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
  have hInit0 :
      C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk0
  have hRawInit0 :
      C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk0
  have hD0 :
      ∀ i, i < 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692))) i := by
    simpa [pk, c13XmssAuthCdAt] using
      SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
        pkSeed pkRoot message sig c13 sigParsed d.lsig0 0
        (sigDataOffset + (1952 + 868 * 0 + 692))
        hParse (by decide : 0 < 2) d.hLayer0 rfl
  have hTreeLt0 :
      C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048) < 2 ^ 256 :=
    c13_adrsXmssTree_lt_of_bounds 0 (digest.hyperIndex / 2048)
      (by decide : 0 < 2 ^ 32)
      (lt_of_le_of_lt (Nat.div_le_self _ _)
        (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
  have hMIdxNorm0 :
      wordNormalize (digest.hyperIndex % 2048) = digest.hyperIndex % 2048 :=
    wordNormalize_mod_2048 digest.hyperIndex
  have hAfterRaw :
      lookupValue
          (SegmentLayer3.afterMerkle
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            11 0 (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath := by
    simpa [pk, digest] using
      c13AfterMerkleRawXmssClimb_of_layer_site_bounded
        pkSeed pkRoot message sig
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
        0 d.lsig0.authPath
        (by decide : 0 < 2) hTreeLt0
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
        (digest.hyperIndex % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk0)
        hD0
        (by simpa [pk, digest] using hInit0 d)
        (by simpa [pk, digest] using hRawInit0 d)
        hMIdxNorm0
  have hRawStep :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            11 0 (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath :=
    c13_stepLayer_merkleNode_eq_xmssClimb_of_afterMerkle
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      _ _ _ _ _ hAfterRaw
  have hMerkle0Root :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        = C13Concrete.wordOfHash16 d.root0 :=
    SegmentAcceptSpec.stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb_wots_success
      pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      forsPk d.wotsPk0 d.root0 d.lsig0.wots d.lsig0.authPath
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          C13Concrete.wotsPkFromSigC13AtLayer_zero] using d.hWots0)
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          C13Concrete.xmssRootFromSigC13AtLayer_zero] using d.hXmss0)
      (by simpa [pk, digest] using hRawStep)
  unfold c13SecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]
  rw [SegmentLayer3.stepLayer_currentNode_eq_merkleNode]
  simpa [pk, digest] using hMerkle0Root

set_option maxHeartbeats 2000000 in
/-- `"d"` binding at the layer-1 lightweight entry state, given the seed-cell
step fact and the layer-0 root `"currentNode"` fact. -/
private theorem probe_d1 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (root0 : Bytes) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig)
    (hStepSeed :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hCurrent :
      lookupValue (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
        "currentNode" = C13Concrete.wordOfHash16 root0) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings "d" =
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
        lsig.wots.count (C13Concrete.wordOfHash16 root0) := by
  rw [probe_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "d" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "d" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13SecondLayerGuardState pkSeed pkRoot message sig) "d"
    (by decide) (by decide)]
  exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
    (c13SecondLayerGuardState pkSeed pkRoot message sig)
    (C13Concrete.wordOfHash16 pkSeed) 1
    (((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
    (((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
    lsig.wots.count
    (C13Concrete.wordOfHash16 root0)
    (c13SecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
      pkSeed pkRoot message sig hStepSeed)
    (c13SecondLayerBeforeDigest_wotsAdrs_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)
    (c13SecondLayerBeforeDigest_currentNode_slot
      pkSeed pkRoot message sig root0 hCurrent)
    (c13SecondLayerBeforeDigest_count_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer1)

set_option maxHeartbeats 2000000 in
/-- `"wotsAdrs"` binding at the layer-1 lightweight entry state. -/
private theorem probe_adrs1 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings "wotsAdrs" =
      C13Concrete.adrsWotsHashBase 1
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048) := by
  rw [probe_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "wotsAdrs" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13SecondLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  rw [probe_beforeDigitLoop_lookup_eq_beforeDigest_of_ne
    (c13SecondLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  exact c13SecondLayerBeforeDigest_wotsAdrs_hyperIndex
    pkSeed pkRoot message sig sigParsed hParse

set_option maxHeartbeats 2000000 in
/-- `"wotsPtr"` value at the layer-1 lightweight entry state. -/
private theorem probe_wptr1 (pkSeed pkRoot message sig : Bytes) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings "wotsPtr" =
      sigDataOffset + (1952 + 868) := by
  rw [probe_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsPtr" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  have hSigBase : evalExpr []
      (SegmentLayer3.afterDigit
        (c13SecondLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigBase") = some sigDataOffset := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigBase") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13SecondLayerGuardState pkSeed pkRoot message sig) "sigBase"
      (by decide) (by decide)]
    rw [SegmentLayer3.beforeDigitLoop_preserves_sigBase]
    rw [c13SecondLayerGuardState_sigBase]
  have hSigOff : evalExpr []
      (SegmentLayer3.afterDigit
        (c13SecondLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigOff") = some 2820 := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigOff") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13SecondLayerGuardState pkSeed pkRoot message sig) "sigOff"
      (by decide) (by decide)]
    rw [probe_beforeDigitLoop_preserves_sigOff]
    rw [c13SecondLayerGuardState_sigOff]
  rw [SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
    _ _ _ _ _ hSigBase hSigOff
    (by decide) (by decide) (by decide)]
  rfl

set_option maxHeartbeats 2000000 in
/-- Frozen calldata at the layer-1 lightweight entry state. -/
private theorem probe_cd1 (pkSeed pkRoot message sig : Bytes) :
    (c13BeforeWotsPkLightState
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  rw [probe_light_world]
  rw [(SegmentLayer3.afterDigit_preserves_selector_calldata
    (c13SecondLayerGuardState pkSeed pkRoot message sig)).2]
  exact c13SecondLayerGuardState_calldata pkSeed pkRoot message sig

set_option maxHeartbeats 2000000 in
/-- Probe twin of the axiom
`c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer1`. -/
theorem probe_c13_layer1 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
        pk digest forsPk sigParsed.layers specRoot,
      ∀ j, (h : j < 43) →
        ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
            (c13BeforeWotsPkLightState
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig)))
            0 43)
          0 43).world.memory (0x40 + 32 * j)).val =
          (InitialNodeKeccak.wotsChainsEnd
            (C13Concrete.wordOfHash16 pkSeed) 1
            ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048)
            (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)[j]'(by
              rw [InitialNodeKeccak.wotsChainsEnd_length]
              omega) := by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold pk digest d
  rw [← c13SecondLayerGuardState_eq_c13LayerLoopState1 pkSeed pkRoot message sig]
  have hStepSeed :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed :=
    c13FirstStepLayer_seed_slot_of_memory_zero pkSeed pkRoot message sig
      (by
        simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using
          c13FirstLayerStep_preserves_memory_zero_of_parse
            pkSeed pkRoot message sig sigParsed hParse)
  have hSeed1 := probe_seed1 pkSeed pkRoot message sig sigParsed hParse
  have hCurrent0Root :=
    probe_current0Root pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold d
  have hD1 := probe_d1 pkSeed pkRoot message sig sigParsed d.root0 d.lsig1
    hParse d.hLayer1 hStepSeed hCurrent0Root
  have hAdrs1 := probe_adrs1 pkSeed pkRoot message sig sigParsed hParse
  have hWPtrVal := probe_wptr1 pkSeed pkRoot message sig
  have hCdSt := probe_cd1 pkSeed pkRoot message sig
  have hHyLt :
      (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).hyperIndex
        < 2 ^ 22 :=
    C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message
  have hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 ((digest.hyperIndex / 2048) / 2048) ((digest.hyperIndex / 2048) % 2048)
        d.lsig1.wots.count (C13Concrete.wordOfHash16 d.root0) < 2 ^ 256 :=
    c13_wotsDigest_lt (C13Concrete.wordOfHash16 pkSeed)
      1 ((digest.hyperIndex / 2048) / 2048) ((digest.hyperIndex / 2048) % 2048)
      d.lsig1.wots.count (C13Concrete.wordOfHash16 d.root0)
  have hAdrsLt :
      C13Concrete.adrsWotsHashBase 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048) < 2 ^ 256 := by
    have hT : ((digest.hyperIndex / 2048) / 2048) <<< 128 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc
        ((digest.hyperIndex / 2048) / 2048) * 2 ^ 128 ≤ 2 ^ 22 * 2 ^ 128 :=
          Nat.mul_le_mul_right _
            (le_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
              (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hHyLt)))
        _ < 2 ^ 256 := by decide
    have hL : ((digest.hyperIndex / 2048) % 2048) <<< 64 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc
        ((digest.hyperIndex / 2048) % 2048) * 2 ^ 64 ≤ 2047 * 2 ^ 64 :=
          Nat.mul_le_mul_right _
            (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 2048)))
        _ < 2 ^ 256 := by decide
    have h224 : (1 : Nat) <<< 224 < 2 ^ 256 := by decide
    exact Nat.bitwise_lt_two_pow
      (Nat.bitwise_lt_two_pow h224 hT) hL
  have e : C13WotsOuterEntry pkSeed
      (c13BeforeWotsPkLightState
        (c13SecondLayerGuardState pkSeed pkRoot message sig))
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 ((digest.hyperIndex / 2048) / 2048) ((digest.hyperIndex / 2048) % 2048)
        d.lsig1.wots.count (C13Concrete.wordOfHash16 d.root0))
      (C13Concrete.adrsWotsHashBase 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048))
      (sigDataOffset + (1952 + 868)) :=
    { seed0 := hSeed1, d0 := hD1, adrs0 := hAdrs1, wptr0 := hWPtrVal }
  exact
    c13Layer1_copyFold43_wotsChainsEnd_cells_of_inputs
      pkSeed pkRoot message sig sigParsed
      (c13BeforeWotsPkLightState
        (c13SecondLayerGuardState pkSeed pkRoot message sig))
      ((digest.hyperIndex / 2048) / 2048) ((digest.hyperIndex / 2048) % 2048)
      (C13Concrete.wordOfHash16 d.root0)
      d.lsig1 hParse d.hLayer1 hDigestLt hAdrsLt e hCdSt

#print axioms probe_c13_layer1

end SphincsMinusVerifiers
