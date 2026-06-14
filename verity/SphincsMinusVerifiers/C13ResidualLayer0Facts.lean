import SphincsMinusVerifiers.C13ResidualLayer0StateFacts
import SphincsMinusVerifiers.SegmentAcceptSpec
import SphincsMinusVerifiers.SiblingCalldata

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

theorem c13Residual_wotsDigest_lt
    (seed : C13Concrete.Word) (layer idxTree idxLeaf count node : Nat) :
    C13Concrete.wotsDigest seed layer idxTree idxLeaf count node < 2 ^ 256 := by
  simpa [C13Concrete.wotsDigest, Compiler.Constants.evmModulus] using
    SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
      [seed, C13Concrete.adrsWotsHashBase layer idxTree idxLeaf, node, count]

theorem c13Residual_afterFinalize_forsPk_of_parse_fors
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature) (forsPk : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk) :
    lookupValue
        (SegmentCompose.afterFinalize
          (mkC13State pkSeed pkRoot message sig)).bindings
        "forsPk" = C13Concrete.wordOfHash16 forsPk := by
  let st := mkC13State pkSeed pkRoot message sig
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hRoots :=
    CurrentNodeFrame.rootCells_eq_forsAllRootsC13_of_hMsg_parse_concrete
      pk message sig hParse
  have hForsPkByte :
      forsPk = C13Concrete.hash16OfWord
        (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors =
        C13Concrete.wordOfHash16 forsPk := by
    rw [hForsPkByte]
    exact (SegmentAcceptSpec.forsPkWordC13_roundtrip pk digest sigParsed.fors).symm
  have hTd :
      lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
        = C13Concrete.idxTree0C13 digest := by
    show lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
        = C13Concrete.idxTree0C13
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
    rw [C13Concrete.parseSignatureC13_R hParse]
    exact CurrentNodeFrame.afterFors_idxTree0_mkC13State pkSeed pkRoot message sig
  have hLd :
      lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
        = C13Concrete.idxLeaf0C13 digest := by
    show lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
        = C13Concrete.idxLeaf0C13
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
    rw [C13Concrete.parseSignatureC13_R hParse]
    exact CurrentNodeFrame.afterFors_idxLeaf0_mkC13State pkSeed pkRoot message sig
  have hTltd : C13Concrete.idxTree0C13 digest < 2 ^ 11 :=
    C13Concrete.idxTree0C13_lt pk sigParsed.R message
  have hForsCompress :
      CurrentNodeFrame.forsPkCompressWord (afterFors st) =
        C13Concrete.wordOfHash16 forsPk := by
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_concrete_mkC13State_six_plus_last
      pkSeed pkRoot message sig digest (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
      (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors) hTd hTltd hLd]
    · simpa [pk, digest, C13Concrete.forsPkWordC13] using hForsPkWord
    · intro j hj
      simpa [pk, digest] using hRoots.1 j hj
    · simpa [pk, digest] using hRoots.2
  exact CurrentNodeFrame.afterFinalize_forsPk_of_compress st forsPk hForsCompress

theorem c13ResidualLayer0BeforeDigest_wotsAdrs_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings
        "wotsAdrs" =
      C13Concrete.adrsWotsHashBase
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) := by
  intro pk digest
  exact SegmentLayer3.beforeDigest_wotsAdrs_eq_of_layer_idxTree
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig)
    0 digest.hyperIndex
    (c13ResidualLayer0GuardState_layer pkSeed pkRoot message sig)
    (c13ResidualLayer0GuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (by decide : 0 < 2 ^ 32)
    (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)

theorem c13ResidualLayer0_wotsAdrs_hyperIndex_norm
    (pkSeed pkRoot message : Bytes) (sigParsed : Signature) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    wordNormalize
        (C13Concrete.adrsWotsHashBase
          0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048))
      =
        C13Concrete.adrsWotsHashBase
          0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) := by
  intro pk digest
  have h128 :
      (digest.hyperIndex / 2048) <<< 128 < 2 ^ 256 := by
    have hnext : digest.hyperIndex / 2048 < 2 ^ 11 := by
      simpa using C13Concrete.hMsgC13_hyperIndex_div_2048_lt pk sigParsed.R message
    rw [Nat.shiftLeft_eq]
    calc
      (digest.hyperIndex / 2048) * 2 ^ 128 < 2 ^ 11 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hnext (by decide)
      _ < 2 ^ 256 := by decide
  have h64 :
      (digest.hyperIndex % 2048) <<< 64 < 2 ^ 256 := by
    have hleaf : digest.hyperIndex % 2048 < 2048 :=
      Nat.mod_lt _ (by decide : 0 < 2048)
    rw [Nat.shiftLeft_eq]
    calc
      (digest.hyperIndex % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hleaf (by decide)
      _ < 2 ^ 256 := by decide
  have h0 : (0 : Nat) <<< 224 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have hinner :
      ((digest.hyperIndex / 2048) <<< 128 |||
          ((digest.hyperIndex % 2048) <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128 h64
  have haddr :
      ((0 : Nat) <<< 224 |||
        ((digest.hyperIndex / 2048) <<< 128 |||
          ((digest.hyperIndex % 2048) <<< 64))) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h0 hinner
  simpa [C13Concrete.adrsWotsHashBase, Nat.lor_assoc] using
    SegmentS2.wordNormalize_of_lt haddr

theorem c13ResidualLayer0BeforeDigest_wotsAdrs_slot_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ((SegmentLayer3.beforeDigest
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).world.memory 0x20).val =
      C13Concrete.adrsWotsHashBase
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) := by
  intro pk digest
  rw [SegmentLayer3.beforeDigest_memory_0x20_eq_of_wotsAdrs
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig)
    (C13Concrete.adrsWotsHashBase
      0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048))
    (c13ResidualLayer0BeforeDigest_wotsAdrs_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)]
  exact c13ResidualLayer0_wotsAdrs_hyperIndex_norm
    pkSeed pkRoot message sigParsed

theorem c13ResidualLayer0BeforeDigest_currentNode_slot
    (pkSeed pkRoot message sig forsPk : Bytes)
    (hForsPk :
      lookupValue
          (SegmentCompose.afterFinalize
            (mkC13State pkSeed pkRoot message sig)).bindings
          "forsPk" = C13Concrete.wordOfHash16 forsPk) :
    ((SegmentLayer3.beforeDigest
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).world.memory 0x40).val =
      C13Concrete.wordOfHash16 forsPk := by
  exact SegmentLayer3.beforeDigest_memory_0x40_eq_wordOfHash16
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig) forsPk
    (by
      rw [c13ResidualLayer0GuardState_currentNode]
      exact hForsPk)

theorem c13ResidualLayer0BeforeDigest_count_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig) :
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings
        "count" = lsig.wots.count := by
  have hSigOffRaw :
      lookupValue (c13ResidualLayer0GuardState pkSeed pkRoot message sig).bindings
          "sigOff" = 1952 := by
    rw [c13ResidualLayer0GuardState_sigOff]
    exact SegmentS2.wordNormalize_of_lt (by decide : 1952 < 2 ^ 256)
  have hRaw :=
    SegmentLayer3.beforeDigest_count_eq_of_sigBase_sigOff_calldata
      (c13ResidualLayer0GuardState pkSeed pkRoot message sig)
      sigDataOffset 1952
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
      (c13ResidualLayer0GuardState_sigBase pkSeed pkRoot message sig)
      hSigOffRaw
      (c13ResidualLayer0GuardState_selector pkSeed pkRoot message sig)
      (c13ResidualLayer0GuardState_calldata pkSeed pkRoot message sig)
      (by decide : sigDataOffset < 2 ^ 256)
      (by decide : 1952 < 2 ^ 256)
      (by decide : 1952 + 688 < 2 ^ 256)
      (by decide :
        sigDataOffset + (1952 + 688) < 2 ^ 256)
  rw [SphincsMinusVerifiers.SiblingCalldata.shr224_calldata_eq_readBE4
      pkSeed pkRoot message sig (1952 + 688)] at hRaw
  have hCountSpec :=
    C13Concrete.parseSignatureC13_layer_wots_count
      hParse (by decide : 0 < 2) hLayer0
  rw [hCountSpec]
  rw [← SphincsMinusVerifiers.SiblingCalldata.readBE4_eq_fold sig (1952 + 688)]
  exact hRaw

theorem c13ResidualLayer0_wotsCount_norm
    (sig : Bytes) (sigParsed : Signature) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig) :
    wordNormalize lsig.wots.count = lsig.wots.count := by
  have hCountSpec :=
    C13Concrete.parseSignatureC13_layer_wots_count
      hParse (by decide : 0 < 2) hLayer0
  rw [hCountSpec]
  rw [← SphincsMinusVerifiers.SiblingCalldata.readBE4_eq_fold sig (1952 + 688)]
  exact SegmentS2.wordNormalize_of_lt
    (lt_trans
      (SphincsMinusVerifiers.SiblingCalldata.readBE_lt sig (1952 + 688) 4)
      (by decide : 256 ^ 4 < 2 ^ 256))

theorem c13ResidualLayer0BeforeDigest_count_slot_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig) :
    ((SegmentLayer3.beforeDigest
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).world.memory 0x60).val =
      lsig.wots.count := by
  rw [SegmentLayer3.beforeDigest_memory_0x60_eq_of_count
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig) lsig.wots.count
    (c13ResidualLayer0BeforeDigest_count_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer0)]
  exact c13ResidualLayer0_wotsCount_norm sig sigParsed lsig hParse hLayer0

end SphincsMinusVerifiers
