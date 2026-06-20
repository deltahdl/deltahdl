#include "elaborator/sequence_composition.h"

namespace delta {

bool IsSequenceCompositionMethodValid(SequenceCompositionMethod method) {
  switch (method) {
    case SequenceCompositionMethod::kNamedInstanceReference:
    case SequenceCompositionMethod::kTriggeredEndPointDetection:
      return true;
  }
  return false;
}

bool NamedSequenceReferenceMatchesFromReferenceTick() { return true; }

bool TriggeredEndPointOperandLegal(SequenceMethodOperandKind kind) {
  // §16.9.11 admits exactly the operand kinds defined for the sequence methods
  // in §16.13.6.
  return IsSequenceMethodOperandLegal(kind);
}

}  // namespace delta
