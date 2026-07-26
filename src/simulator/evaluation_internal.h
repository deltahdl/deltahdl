#pragma once

#include "common/types.h"
#include "lexer/token.h"

namespace delta {

class Arena;

// Operator-evaluation primitives shared between evaluation.cpp (expression-node
// evaluators) and evaluation_ops.cpp (scalar/vector operator implementations).
// These are defined exactly once, in evaluation_ops.cpp.

Logic4Vec EvalUnaryOp(TokenKind op, Logic4Vec operand, Arena& arena);

Logic4Vec ExtendVec(const Logic4Vec& v, uint32_t target_width, bool sign_ext,
                    Arena& arena);

bool EvalCaseEquality(Logic4Vec lhs, Logic4Vec rhs);

// Decodes the bit pattern a real vector carries: a 32-bit vector holds a
// shortreal (float) pattern, any other width a real (double) one. The caller
// decides what a non-real vector contributes, so `v.is_real` shall hold.
double RealVecToDouble(const Logic4Vec& v);

}  // namespace delta
