import SphincsMinusVerifiers.C13ResidualInterface
import SphincsMinusVerifiers.CurrentNodeFrame

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

private theorem runtimeState_with_bindings_selector
    (st : RuntimeState) (bindings : List (String × Nat)) :
    ({ st with bindings := bindings } : RuntimeState).selector = st.selector := rfl

private theorem runtimeState_with_bindings_calldata
    (st : RuntimeState) (bindings : List (String × Nat)) :
    ({ st with bindings := bindings } : RuntimeState).world.calldata =
      st.world.calldata := rfl

private theorem loopState_selector
    (varName : String) (st : RuntimeState) (index : Nat) :
    (ClimbLoopGuarded.loopState varName st index).selector = st.selector := rfl

private theorem loopState_calldata
    (varName : String) (st : RuntimeState) (index : Nat) :
    (ClimbLoopGuarded.loopState varName st index).world.calldata =
      st.world.calldata := rfl

def c13ResidualLayer0GuardState
    (pkSeed pkRoot message sig : Bytes) : RuntimeState :=
  ClimbLoopGuarded.loopState "layer"
    { (SegmentCompose.afterSeed (mkC13State pkSeed pkRoot message sig)) with
      bindings :=
        bindValue
          (SegmentCompose.afterSeed
            (mkC13State pkSeed pkRoot message sig)).bindings
          "layer" (wordNormalize 0) } 0

theorem c13ResidualLayer0GuardState_eq_c13LayerLoopState0
    (pkSeed pkRoot message sig : Bytes) :
    c13ResidualLayer0GuardState pkSeed pkRoot message sig =
      CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig) := rfl

theorem c13ResidualLayer0GuardState_seed_slot
    (pkSeed pkRoot message sig : Bytes) :
    ((c13ResidualLayer0GuardState pkSeed pkRoot message sig).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  unfold c13ResidualLayer0GuardState
  rw [ClimbLoopGuarded.loopState_preserves_memory_val]
  rw [MemoryKit.withBindings_preserves_memory_val]
  exact CurrentNodeFrame.afterSeed_seed_slot_mkC13State pkSeed pkRoot message sig

theorem c13ResidualLayer0BeforeDigest_seed_slot
    (pkSeed pkRoot message sig : Bytes) :
    ((SegmentLayer3.beforeDigest
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [SegmentLayer3.beforeDigest_preserves_memory_zero]
  exact c13ResidualLayer0GuardState_seed_slot pkSeed pkRoot message sig

theorem c13ResidualLayer0GuardState_currentNode
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13ResidualLayer0GuardState pkSeed pkRoot message sig).bindings
        "currentNode" =
      lookupValue
        (SegmentCompose.afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings
        "forsPk" := by
  unfold c13ResidualLayer0GuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]
  exact CurrentNodeFrame.afterSeed_currentNode
    (mkC13State pkSeed pkRoot message sig)

theorem c13ResidualLayer0GuardState_idxTree
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13ResidualLayer0GuardState pkSeed pkRoot message sig).bindings
        "idxTree" =
      lookupValue
        (SegmentCompose.afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings
        "htIdx" := by
  unfold c13ResidualLayer0GuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "idxTree" _ (by decide)]
  exact CurrentNodeFrame.afterSeed_idxTree
    (mkC13State pkSeed pkRoot message sig)

theorem c13ResidualLayer0GuardState_idxTree_hyperIndex
    (pkSeed pkRoot message sig : Bytes) {sigParsed : Signature}
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue (c13ResidualLayer0GuardState pkSeed pkRoot message sig).bindings
        "idxTree"
      =
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex := by
  rw [c13ResidualLayer0GuardState_idxTree]
  rw [CurrentNodeFrame.afterFinalize_htIdx_mkC13State]
  rw [C13Concrete.parseSignatureC13_R hParse]
  rfl

theorem c13ResidualLayer0GuardState_sigOff
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13ResidualLayer0GuardState pkSeed pkRoot message sig).bindings
        "sigOff" = wordNormalize 1952 := by
  unfold c13ResidualLayer0GuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigOff" _ (by decide)]
  exact CurrentNodeFrame.afterSeed_sigOff
    (mkC13State pkSeed pkRoot message sig)

theorem c13ResidualLayer0GuardState_sigBase
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13ResidualLayer0GuardState pkSeed pkRoot message sig).bindings
        "sigBase" = sigDataOffset := by
  unfold c13ResidualLayer0GuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigBase" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigBase" _ (by decide)]
  exact CurrentNodeFrame.afterSeed_sigBase_mkC13State pkSeed pkRoot message sig

theorem c13ResidualLayer0GuardState_layer
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13ResidualLayer0GuardState pkSeed pkRoot message sig).bindings
        "layer" = 0 := by
  unfold c13ResidualLayer0GuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_self]
  exact SegmentS2.wordNormalize_of_lt (by decide : 0 < 2 ^ 256)

theorem c13ResidualLayer0GuardState_selector
    (pkSeed pkRoot message sig : Bytes) :
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig).selector = 0 := by
  unfold c13ResidualLayer0GuardState
  rw [loopState_selector, runtimeState_with_bindings_selector]
  exact CurrentNodeFrame.afterSeed_selector_mkC13State pkSeed pkRoot message sig

theorem c13ResidualLayer0GuardState_calldata
    (pkSeed pkRoot message sig : Bytes) :
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold c13ResidualLayer0GuardState
  rw [loopState_calldata, runtimeState_with_bindings_calldata]
  exact CurrentNodeFrame.afterSeed_calldata_mkC13State pkSeed pkRoot message sig

end SphincsMinusVerifiers
