import SphincsMinusVerifiers.C13ResidualLayer1FirstStateFacts

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State

def c13ResidualSecondLayerGuardState
    (pkSeed pkRoot message sig : Bytes) : RuntimeState :=
  ClimbLoopGuarded.loopState "layer"
    (SegmentLayer3.stepLayer
      (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)) 1

theorem c13SecondLayerGuardState_shape
    (pkSeed pkRoot message sig : Bytes) :
    c13ResidualSecondLayerGuardState pkSeed pkRoot message sig =
      ClimbLoopGuarded.loopState "layer"
        (SegmentLayer3.stepLayer
          (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)) 1 := rfl

theorem c13ResidualSecondLayerGuardState_eq_c13LayerLoopState1
    (pkSeed pkRoot message sig : Bytes) :
    c13ResidualSecondLayerGuardState pkSeed pkRoot message sig =
      CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig) := by
  unfold c13ResidualSecondLayerGuardState c13ResidualFirstLayerGuardState
  unfold CurrentNodeFrame.c13LayerLoopState1
  unfold CurrentNodeFrame.c13LayerAfterStep0
  rw [c13ResidualLayer0GuardState_eq_c13LayerLoopState0]
  unfold ClimbLoopGuarded.loopState
  rfl

end SphincsMinusVerifiers
