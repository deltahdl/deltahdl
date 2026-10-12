#pragma once

#include <cstdint>

#include "common/types.h"
#include "lexer/token.h"

namespace delta {

class Arena;
class SimContext;
struct Expr;

// Operator-evaluation primitives shared between evaluation.cpp (expression-node
// evaluators) and evaluation_ops.cpp (scalar/vector operator implementations).
// These are defined exactly once, in evaluation_ops.cpp.

Logic4Vec EvalUnaryOp(TokenKind op, Logic4Vec operand, Arena& arena);

// §11.4.7: an operand's truth value. A real one is true where it is not 0.0,
// -0.0 among the zeros; an integral one is true where any bit is a known 1,
// false where every bit is a known 0, and ambiguous otherwise, every word
// taking part. Defined in evaluation_ops.cpp.
enum class Truth : uint8_t { kFalse, kTrue, kAmbiguous };
Truth TruthOf(const Logic4Vec& v);

// The one-bit 0, 1 or x a truth value is. Defined in evaluation_ops.cpp.
Logic4Vec TruthBit(Truth t, Arena& arena);

Logic4Vec ExtendVec(const Logic4Vec& v, uint32_t target_width, bool sign_ext,
                    Arena& arena);

bool EvalCaseEquality(Logic4Vec lhs, Logic4Vec rhs);

// §11.4.11: a conditional expression, defined in eval_ternary.cpp; a
// context_width of 0 is a self-determined one, and `unsigned_context` says
// that §11.8.2 propagates an unsigned type down to it.
Logic4Vec EvalTernary(const Expr* expr, SimContext& ctx, Arena& arena,
                      uint32_t context_width, bool unsigned_context);

// §11.8.2: EvalExpr for a context-determined operand, which takes the type the
// expression it stands in propagates down to it as well as the size: where
// `unsigned_context` is set, a signed operand is extended by zero and its
// operator applied as an unsigned one. Defined in evaluation.cpp.
Logic4Vec EvalExprInContext(const Expr* expr, SimContext& ctx, Arena& arena,
                            uint32_t context_width, bool unsigned_context);

// §11.6.1 Table 11-21's classes of operator and §11.8.1's self-determined
// type of an expression as its form gives it. Defined in
// evaluation_self_type.cpp.
bool IsMaxWidthBinaryOp(TokenKind op);
bool IsLeftWidthBinaryOp(TokenKind op);
bool IsUnaryReductionOp(TokenKind op);
uint32_t SimSelfWidth(const Expr* expr, SimContext& ctx);
bool SimSelfSigned(const Expr* expr, SimContext& ctx);
bool SimSelfReal(const Expr* expr, SimContext& ctx);

}  // namespace delta
