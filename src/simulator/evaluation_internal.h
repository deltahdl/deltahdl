#pragma once

#include <cstdint>

#include "common/types.h"
#include "lexer/token.h"

namespace delta {

class Arena;
class SimContext;
struct Expr;
struct SelfType;

Logic4Vec EvalUnaryOp(TokenKind op, Logic4Vec operand, Arena& arena);

enum class Truth : uint8_t { kFalse, kTrue, kAmbiguous };
Truth TruthOf(const Logic4Vec& v);

Logic4Vec TruthBit(Truth t, Arena& arena);

inline Truth ClauseConjunction(Truth first, Truth second) {
  if (first == Truth::kFalse || second == Truth::kFalse) return Truth::kFalse;
  return first == Truth::kAmbiguous || second == Truth::kAmbiguous
             ? Truth::kAmbiguous
             : Truth::kTrue;
}

Logic4Vec ExtendVec(const Logic4Vec& v, uint32_t target_width, bool sign_ext,
                    Arena& arena);

bool EvalCaseEquality(Logic4Vec lhs, Logic4Vec rhs);

Logic4Vec EvalTernary(const Expr* expr, SimContext& ctx, Arena& arena,
                      uint32_t context_width, bool unsigned_context);

Logic4Vec EvalExprInContext(const Expr* expr, SimContext& ctx, Arena& arena,
                            uint32_t context_width, bool unsigned_context);

uint32_t SimSelfWidth(const Expr* expr, SimContext& ctx);
bool SimSelfSigned(const Expr* expr, SimContext& ctx);
bool SimSelfReal(const Expr* expr, SimContext& ctx);
bool SimSelf4State(const Expr* expr, SimContext& ctx);

SelfType CastSelfType(const Expr* cast, SimContext& ctx);

}  // namespace delta
