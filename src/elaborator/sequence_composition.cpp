#include "elaborator/sequence_composition.h"

#include "elaborator/sequence_method.h"

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
  return IsSequenceMethodOperandLegal(kind);
}

}  // namespace delta
