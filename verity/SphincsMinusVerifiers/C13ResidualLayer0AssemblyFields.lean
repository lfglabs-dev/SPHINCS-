import SphincsMinusVerifiers.C13ResidualLayer0Inputs

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbLoop (foldLoop)
open SphincsMinusVerifiers.MkC13State

set_option maxHeartbeats 2000000 in
theorem c13_layer0_exact_seed_field
    (pkSeed pkRoot message sig : Bytes) :
    ∀ j, j < 43 →
      ((foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
          (c13BeforeWotsPkLightState
            (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) 0 j).world.memory
          0x00).val =
        C13Concrete.wordOfHash16 pkSeed := by
  intro j hj
  rw [wotsOuterFold_preserves_seed_cell
    (c13BeforeWotsPkLightState
      (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) j (by omega)]
  exact c13_layer0_light_seed0 pkSeed pkRoot message sig

set_option maxHeartbeats 2000000 in
theorem c13_layer0_exact_d_field
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk)
    (hLayer0 : sigParsed.layers[0]? = some lsig) :
    ∀ j, j < 43 →
      lookupValue
          (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
            (c13BeforeWotsPkLightState
              (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) 0 j).bindings "d" =
        C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
          0
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
          lsig.wots.count (C13Concrete.wordOfHash16 forsPk) := by
  intro j _hj
  rw [wotsOuterFold_preserves_binding
    (c13BeforeWotsPkLightState
      (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) "d"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j]
  exact c13_layer0_light_d0 pkSeed pkRoot message sig sigParsed forsPk lsig
    hParse hFors hLayer0

set_option maxHeartbeats 2000000 in
theorem c13_layer0_exact_adrs_field
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    ∀ j, j < 43 →
      lookupValue
          (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
            (c13BeforeWotsPkLightState
              (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) 0 j).bindings
          "wotsAdrs" =
        C13Concrete.adrsWotsHashBase 0
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048) := by
  intro j _hj
  rw [wotsOuterFold_preserves_binding
    (c13BeforeWotsPkLightState
      (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) "wotsAdrs"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j]
  exact c13_layer0_light_adrs0 pkSeed pkRoot message sig sigParsed hParse

set_option maxHeartbeats 2000000 in
theorem c13_layer0_exact_wptr_field
    (pkSeed pkRoot message sig : Bytes) :
    ∀ j, j < 43 →
      lookupValue
          (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
            (c13BeforeWotsPkLightState
              (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) 0 j).bindings
          "wotsPtr" =
        lookupValue
          (c13BeforeWotsPkLightState
            (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings
          "wotsPtr" := by
  intro j _hj
  rw [wotsOuterFold_preserves_binding
    (c13BeforeWotsPkLightState
      (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) "wotsPtr"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j]

set_option maxHeartbeats 2000000 in
theorem c13_layer0_exact_cdload_field
    (pkSeed pkRoot message sig : Bytes) :
    ∀ j, j < 43 → ∀ (s : RuntimeState),
      lookupValue s.bindings "wotsPtr" =
        lookupValue
          (c13BeforeWotsPkLightState
            (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings
          "wotsPtr" →
      lookupValue s.bindings "i" = j →
      s.world =
        (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
          (c13BeforeWotsPkLightState
            (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) 0 j).world →
      evalExpr [] s
          (.calldataload
            (.add (.localVar "wotsPtr")
              (.shl (.literal 4) (.localVar "i")))) =
        some (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
          (sigDataOffset + (1952 + 16 * j))) := by
  intro j hj s h1 h2 h3
  have hWPtrVal :
      lookupValue
          (c13BeforeWotsPkLightState
            (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings
          "wotsPtr" = sigDataOffset + 1952 :=
    c13_layer0_light_wptr0 pkSeed pkRoot message sig
  have hCdSt :
      (c13BeforeWotsPkLightState
          (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).world.calldata =
        headWords pkSeed pkRoot message sig.size ++ bytesToWords sig :=
    c13_layer0_light_cd0 pkSeed pkRoot message sig
  exact wotsOuterFold_cdload_raw pkSeed pkRoot message sig
    (c13BeforeWotsPkLightState
      (c13ResidualLayer0GuardState pkSeed pkRoot message sig)) 1952
    (by decide) hCdSt j hj s (h1.trans hWPtrVal) h2 h3

end SphincsMinusVerifiers
