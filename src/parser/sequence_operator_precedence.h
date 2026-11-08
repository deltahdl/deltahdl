#pragma once

#include <cstdint>

#include "lexer/token.h"

namespace delta {

enum class SequenceOperator : uint8_t {
  kRepetition,
  kCycleDelay,
  kThroughout,
  kWithin,
  kIntersect,
  kAnd,
  kOr,
};

enum class SequenceOperatorAssoc : uint8_t {
  kNone,
  kLeft,
  kRight,
};

int SequenceOperatorPrecedence(SequenceOperator op);

SequenceOperatorAssoc SequenceOperatorAssociativity(SequenceOperator op);

bool SequenceOperatorBindsTighter(SequenceOperator a, SequenceOperator b);

bool SequenceOperatorFromToken(TokenKind kind, SequenceOperator* out);

}  // namespace delta
