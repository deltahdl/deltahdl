#pragma once

#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

class SimContext;
class Arena;
struct Logic4Vec;

struct LinearSequence {
  std::vector<Expr*> operands;
  std::vector<SeqCycleDelay> delays;
  std::vector<std::vector<SeqMatchAssign>> match_items;
  std::vector<SeqRepetition> repetitions;
  std::vector<std::vector<EventExpr>> operand_clocks;
  std::vector<int> operand_clock_index;
  std::vector<EventExpr> clock_out;
  int clock_out_index = 0;
  std::vector<EventExpr> declared_clock;
  std::vector<SeqLocalDecl> locals;
  std::vector<SeqThroughout> throughouts;
  std::vector<EventExpr> clock;
  std::vector<LinearSequence> intersects;
  std::vector<LinearSequence> conjuncts;
  std::vector<LinearSequence> alternatives;
  bool first_match = false;
  std::vector<std::pair<const Expr*, std::shared_ptr<const LinearSequence>>>
      nested;
};

void ForEachLinearSequenceExpr(const LinearSequence& body,
                               const std::function<void(const Expr*)>& fn);

bool FlattenLinearSequence(const ModuleItem* seq, SimContext& ctx, Arena& arena,
                           LinearSequence& out);

const LinearSequence* NestedOperand(const LinearSequence& body, size_t pos);

const std::vector<EventExpr>& OperandClock(const LinearSequence& body,
                                           size_t pos);
int OperandClockIndex(const LinearSequence& body, size_t pos);

bool NamesAnotherClock(const LinearSequence& body);

std::vector<EventExpr> SubstituteClock(const std::vector<EventExpr>& clock,
                                       const ActualsByFormal& actuals,
                                       Arena& arena);

ActualsByFormal BindInstanceActuals(const ModuleItem* decl,
                                    const Expr* instance, Arena& arena);

LinearSequence SubstituteLinearSequence(const LinearSequence& body,
                                        const ActualsByFormal& actuals,
                                        SimContext& ctx, Arena& arena);

ActualsByFormal CheckerTreeActuals(const std::string& inst_prefix,
                                   SimContext& ctx);

Expr* LiteralOfValue(const Logic4Vec& value, Arena& arena);

}  // namespace delta
