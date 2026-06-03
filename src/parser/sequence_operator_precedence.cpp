#include "parser/sequence_operator_precedence.h"

namespace delta {

int SequenceOperatorPrecedence(SequenceOperator op) {
  // Table 16-1 runs from highest precedence to lowest. Assign descending
  // integer levels so that the topmost row (repetition) yields the largest
  // value and the bottom row (or) the smallest. The gaps are uniform; only the
  // ordering is consumed by callers.
  switch (op) {
    case SequenceOperator::kRepetition:
      return 7;
    case SequenceOperator::kCycleDelay:
      return 6;
    case SequenceOperator::kThroughout:
      return 5;
    case SequenceOperator::kWithin:
      return 4;
    case SequenceOperator::kIntersect:
      return 3;
    case SequenceOperator::kAnd:
      return 2;
    case SequenceOperator::kOr:
      return 1;
  }
  return 0;
}

SequenceOperatorAssoc SequenceOperatorAssociativity(SequenceOperator op) {
  switch (op) {
    case SequenceOperator::kRepetition:
      return SequenceOperatorAssoc::kNone;
    case SequenceOperator::kThroughout:
      return SequenceOperatorAssoc::kRight;
    case SequenceOperator::kCycleDelay:
    case SequenceOperator::kWithin:
    case SequenceOperator::kIntersect:
    case SequenceOperator::kAnd:
    case SequenceOperator::kOr:
      return SequenceOperatorAssoc::kLeft;
  }
  return SequenceOperatorAssoc::kNone;
}

bool SequenceOperatorBindsTighter(SequenceOperator a, SequenceOperator b) {
  return SequenceOperatorPrecedence(a) > SequenceOperatorPrecedence(b);
}

bool SequenceOperatorFromToken(TokenKind kind, SequenceOperator* out) {
  switch (kind) {
    case TokenKind::kHashHash:
      *out = SequenceOperator::kCycleDelay;
      return true;
    case TokenKind::kKwThroughout:
      *out = SequenceOperator::kThroughout;
      return true;
    case TokenKind::kKwWithin:
      *out = SequenceOperator::kWithin;
      return true;
    case TokenKind::kKwIntersect:
      *out = SequenceOperator::kIntersect;
      return true;
    case TokenKind::kKwAnd:
      *out = SequenceOperator::kAnd;
      return true;
    case TokenKind::kKwOr:
      *out = SequenceOperator::kOr;
      return true;
    default:
      return false;
  }
}

}  // namespace delta
