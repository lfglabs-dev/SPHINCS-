import SphincsMinusVerifiers.C13ResidualLayer0StateFacts

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics

abbrev c13ResidualFirstLayerGuardState :
    Bytes → Bytes → Bytes → Bytes → RuntimeState :=
  c13ResidualLayer0GuardState

end SphincsMinusVerifiers
