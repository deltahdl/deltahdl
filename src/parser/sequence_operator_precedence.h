#pragma once

#include <cstdint>

#include "lexer/token.h"

namespace delta {

// §16.9.1 / Table 16-1: the operators that combine sequence operations,
// enumerated here from highest precedence (kRepetition) down to lowest (kOr),
// matching the order in which Table 16-1 lists them. kRepetition stands for the
// [*], [=], and [->] forms; the lexer emits those as bracketed multi-token runs
// rather than a single operator token, so they are represented as one category.
enum class SequenceOperator : uint8_t {
  kRepetition,  // [*] [=] [->]
  kCycleDelay,  // ##
  kThroughout,  // throughout
  kWithin,      // within
  kIntersect,   // intersect
  kAnd,         // and
  kOr,          // or
};

// §16.9.1: the associativity column of Table 16-1. The repetition operators
// carry no associativity (shown as "—"); the cycle-delay operator and the and,
// or, within, and intersect operators associate left; throughout associates
// right.
enum class SequenceOperatorAssoc : uint8_t {
  kNone,
  kLeft,
  kRight,
};

// §16.9.1: the precedence level of a sequence operator. A larger value binds
// more tightly. Table 16-1 lists the highest-precedence operator first, so
// kRepetition produces the largest level and kOr the smallest. Only the
// relative ordering of the returned values is meaningful.
int SequenceOperatorPrecedence(SequenceOperator op);

// §16.9.1: the associativity of a sequence operator, per Table 16-1.
SequenceOperatorAssoc SequenceOperatorAssociativity(SequenceOperator op);

// §16.9.1: true when operator `a` binds strictly more tightly than `b`, i.e.
// `a` sits higher in Table 16-1. Distinct sequence operators always have
// distinct precedence, so this strict comparison fully orders any two of them.
bool SequenceOperatorBindsTighter(SequenceOperator a, SequenceOperator b);

// Resolves a single-token sequence operator — the cycle-delay `##` and the
// keyword operators throughout, within, intersect, and, or — to its Table 16-1
// category. Returns false for any other token. The repetition operators are
// bracketed and never arrive here as one token, so they have no token mapping.
bool SequenceOperatorFromToken(TokenKind kind, SequenceOperator* out);

}  // namespace delta
