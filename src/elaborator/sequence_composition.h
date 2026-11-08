#pragma once

#include <cstdint>

#include "elaborator/sequence_method.h"

namespace delta {

enum class SequenceCompositionMethod : uint8_t {
  kNamedInstanceReference,
  kTriggeredEndPointDetection,
};

bool IsSequenceCompositionMethodValid(SequenceCompositionMethod method);

bool NamedSequenceReferenceMatchesFromReferenceTick();

bool TriggeredEndPointOperandLegal(SequenceMethodOperandKind kind);

}  // namespace delta
