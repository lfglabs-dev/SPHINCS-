import SphincsMinusVerifiers.C13ResidualLayer0AssemblyFields

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

set_option maxHeartbeats 2000000 in
theorem c13_ok_beforeAuthOff_wotsPk_lightweight_chain_inputs_layer0_proved :
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
      let st :=
        c13BeforeWotsPkLightState
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig))
      let wotsPtr := lookupValue st.bindings "wotsPtr"
      C13WotsOuterExactInputs pkSeed pkRoot message sig st
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk) wotsPtr 1952 := by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse _hZero hFors _hFold pk digest d
  rw [← c13ResidualLayer0GuardState_eq_c13LayerLoopState0 pkSeed pkRoot message sig]
  intro st wotsPtr
  refine
    { hSeed := c13_layer0_exact_seed_field pkSeed pkRoot message sig,
      hD := c13_layer0_exact_d_field pkSeed pkRoot message sig sigParsed forsPk d.lsig0
        hParse hFors d.hLayer0,
      hAdrs := c13_layer0_exact_adrs_field pkSeed pkRoot message sig sigParsed hParse,
      hWPtr := c13_layer0_exact_wptr_field pkSeed pkRoot message sig,
      hCdLoad := c13_layer0_exact_cdload_field pkSeed pkRoot message sig }

#print axioms c13_ok_beforeAuthOff_wotsPk_lightweight_chain_inputs_layer0_proved

end SphincsMinusVerifiers
