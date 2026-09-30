#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

class Arena;

// The path `base.member`, written at `loc`, as the parser reads it; a caller
// naming a package member sets is_scope_resolution for `base::member`.
Expr* MemberOf(std::string_view base, std::string_view member, SourceLoc loc,
               Arena& arena);

// Each expression slot of a list of clocking events, the signal and the iff
// condition of each.
template <typename Fn>
void ForEachEventSlot(std::vector<EventExpr>& events, const Fn& fn) {
  for (EventExpr& ev : events) {
    fn(ev.signal);
    fn(ev.iff_condition);
  }
}

// Each expression slot of the match items of one operand.
template <typename Fn>
void ForEachItemSlot(std::vector<SeqMatchAssign>& items, const Fn& fn) {
  for (SeqMatchAssign& item : items) {
    fn(item.rhs);
    fn(item.call);
  }
}

// Each expression slot of a sequence body, those of its intersects,
// conjuncts and alternatives included, for a substitution to replace.
template <typename Fn>
void ForEachBodySlot(SeqLinearBody& body, const Fn& fn) {
  for (Expr*& operand : body.operands) fn(operand);
  for (auto& items : body.match_items) ForEachItemSlot(items, fn);
  ForEachItemSlot(body.first_match_items, fn);
  for (SeqLocalDecl& local : body.locals) fn(local.init);
  for (SeqThroughout& guard : body.throughouts) fn(guard.cond);
  for (auto& clock : body.clocks) ForEachEventSlot(clock, fn);
  ForEachEventSlot(body.clock_out, fn);
  for (SeqLinearBody& inner : body.intersects) ForEachBodySlot(inner, fn);
  for (SeqLinearBody& inner : body.conjuncts) ForEachBodySlot(inner, fn);
  for (SeqLinearBody& inner : body.alternatives) ForEachBodySlot(inner, fn);
}

// Each expression slot of the tree under `node`, its sequences' included.
template <typename Fn>
void ForEachTreeSlot(PropertyExprNode* node, const Fn& fn) {
  fn(node->boolean);
  fn(node->range_min);
  fn(node->range_max);
  for (auto& values : node->case_values) {
    for (Expr*& value : values) fn(value);
  }
  ForEachEventSlot(node->clock, fn);
  if (node->sequence != nullptr) {
    ForEachBodySlot(node->sequence->seq_linear, fn);
    ForEachEventSlot(node->sequence->seq_clock, fn);
  }
  for (PropertyExprNode* operand : node->operands) {
    ForEachTreeSlot(operand, fn);
  }
}

// The names a sequence body declares as its local variables.
void CollectBodyLocals(const SeqLinearBody& body,
                       std::unordered_set<std::string_view>& out);

// The locals the sequences of the tree under `node` declare.
void CollectTreeLocals(const PropertyExprNode* node,
                       std::unordered_set<std::string_view>& out);

}  // namespace delta
