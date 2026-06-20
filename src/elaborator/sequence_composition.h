#pragma once

#include <cstdint>

#include "elaborator/multiclock_endpoint.h"
#include "elaborator/sequence_method.h"

namespace delta {

// §16.9.11 describes composing a complex sequence from simpler subsequences. It
// uses the `triggered` method defined in §16.13.6 (see
// "elaborator/sequence_method.h") and the ending-clock rule shared with
// §16.13.5 (see "elaborator/multiclock_endpoint.h").

// §16.9.11: a complex sequence can be composed from simpler subsequences in one
// of two ways.
enum class SequenceCompositionMethod : uint8_t {
  // Instantiate a named sequence by referencing its name.
  kNamedInstanceReference,
  // Detect the end point of another sequence using the `triggered` method.
  kTriggeredEndPointDetection,
};

// §16.9.11: both composition forms are valid ways of building a complex
// sequence. Returns true for either enumerated method.
bool IsSequenceCompositionMethodValid(SequenceCompositionMethod method);

// §16.9.11: instantiating a named sequence by referencing its name requires the
// referenced sequence to match starting from the clock tick at which the
// reference is reached during evaluation of the enclosing sequence. Returns
// true to assert that the match start is anchored at the reference tick (not at
// the enclosing sequence's start).
bool NamedSequenceReferenceMatchesFromReferenceTick();

// §16.9.11: detecting the reaching of a sequence's end point is done with the
// `triggered` method, applied to a named sequence instance (with or without
// arguments), an untyped formal argument, or a formal argument of type
// `sequence`. Shares the operand legality rule with §16.13.6.
bool TriggeredEndPointOperandLegal(SequenceMethodOperandKind kind);

}  // namespace delta
