#pragma once

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/sim_context.h"

namespace delta {

// §16.10 and §6.8: the width of a local declared with a data type keyword,
// 1 for a bit type.
uint32_t LocalWidth(TokenKind type_kw);

// §16.10 and §6.8: the state of a local declared with a data type keyword,
// and the value it holds before any assignment, x for a 4-state type and 0
// for a 2-state one.
bool LocalIs4State(TokenKind type_kw);

// §16.10: the values a new attempt's copies of the locals `decls` begin with.
std::vector<Logic4Vec> InitialLocals(const std::vector<SeqLocalDecl>& decls,
                                     SimContext& ctx, Arena& arena);

// §16.11: schedules a subroutine call attached to a sequence for the match
// being read now.
void ScheduleMatchCall(const Expr* call, SimContext& ctx, Arena& arena);

}  // namespace delta
