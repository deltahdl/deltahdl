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

}  // namespace delta
