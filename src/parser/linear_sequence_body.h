#pragma once

#include <cstddef>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

bool IsNoDelay(const SeqCycleDelay& delay);

SeqCycleDelay AddSeqDelays(const SeqCycleDelay& a, const SeqCycleDelay& b);

void PushOperandClock(SeqLinearBody& body, const std::vector<EventExpr>& clock);

bool UnrollGroupRepetition(SeqLinearBody& body, size_t first,
                           const SeqRepetition& rep);

void MarkEmptyMatchItems(const SeqLinearBody& body, size_t first,
                         std::vector<SeqMatchAssign>& items);

void WrapWithinOperand(SeqLinearBody& body, Expr* lead, Expr* trail);

}  // namespace delta
