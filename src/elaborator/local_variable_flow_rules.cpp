#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using NameSet = std::unordered_set<std::string_view>;
using SequenceMap = std::unordered_map<std::string_view, const ModuleItem*>;

// One reference to a local variable at a point no assignment reaches.
struct Unassigned {
  std::string_view name;
  SourceLoc loc;
  const char* clause = "16.10";
};

// §16.10 with Annex F.5.4: the walk of a body in order, carrying the local
// variables assigned at each point. `tracked` holds the locals the walk
// judges, those with no initialization assignment; every reference to one
// at a point it is not assigned is added to `found`.
struct Flow {
  const SequenceMap& sequences;
  const NameSet& tracked;
  std::vector<Unassigned>& found;
  // The clause a reference found now is reported under: §16.8.2 for the
  // actual of an input or inout local variable formal argument.
  const char* clause = "16.10";
};

void CheckReads(const Expr* e, const NameSet& assigned, Flow& flow) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier && flow.tracked.count(e->text) != 0 &&
      assigned.count(e->text) == 0) {
    flow.found.push_back({e->text, e->range.start, flow.clause});
  }
  if (e->kind == ExprKind::kMemberAccess) {
    CheckReads(e->lhs, assigned, flow);
    return;
  }
  ForEachExprChild(
      e, [&](const Expr* child) { CheckReads(child, assigned, flow); });
}

const ModuleItem* SequenceOf(const Expr* e, const SequenceMap& sequences) {
  if (e != nullptr && e->kind == ExprKind::kMemberAccess) e = e->lhs;
  if (e == nullptr || e->kind != ExprKind::kCall) return nullptr;
  auto it = sequences.find(e->callee);
  return it == sequences.end() ? nullptr : it->second;
}

// Whether a match item of `body` assigns `name`.
bool ItemsAssign(const std::vector<SeqMatchAssign>& items,
                 std::string_view name) {
  for (const SeqMatchAssign& item : items) {
    if (!item.init && item.lvar == name) return true;
  }
  return false;
}

bool BodyAssigns(const SeqLinearBody& body, std::string_view name) {
  if (ItemsAssign(body.first_match_items, name)) return true;
  for (const auto& items : body.match_items) {
    if (ItemsAssign(items, name)) return true;
  }
  for (const auto* nested :
       {&body.intersects, &body.conjuncts, &body.alternatives}) {
    for (const SeqLinearBody& inner : *nested) {
      if (BodyAssigns(inner, name)) return true;
    }
  }
  return false;
}

// §16.8.2 and §16.10: whether the formal `i` of `seq` gives the local
// variable bound to it a value rather than reading it: an output or inout
// local variable formal argument, or an untyped formal the body assigns.
bool FormalAssigns(const ModuleItem* seq, size_t i) {
  size_t local_index = 0;
  for (size_t j = 0; j < i && j < seq->prop_formal_is_local.size(); ++j) {
    if (seq->prop_formal_is_local[j]) ++local_index;
  }
  if (i < seq->prop_formal_is_local.size() && seq->prop_formal_is_local[i]) {
    Direction dir = local_index < seq->prop_seq_local_lvar_directions.size()
                        ? seq->prop_seq_local_lvar_directions[local_index]
                        : Direction::kInput;
    return dir == Direction::kOutput;
  }
  return BodyAssigns(seq->seq_linear, seq->prop_formals[i]);
}

// An operand of a body: an instance's actuals are read, but for a local
// bound whole to a formal that gives it a value, which is assigned after the
// operand.
void FlowOperand(const Expr* operand, NameSet& assigned, Flow& flow,
                 std::vector<std::string_view>& given) {
  const ModuleItem* seq = SequenceOf(operand, flow.sequences);
  if (seq == nullptr) {
    CheckReads(operand, assigned, flow);
    return;
  }
  const Expr* call =
      operand->kind == ExprKind::kMemberAccess ? operand->lhs : operand;
  for (size_t i = 0; i < call->args.size(); ++i) {
    const Expr* arg = call->args[i];
    if (arg != nullptr && arg->kind == ExprKind::kIdentifier &&
        i < seq->prop_formals.size() && FormalAssigns(seq, i)) {
      given.push_back(arg->text);
      continue;
    }
    bool local =
        i < seq->prop_formal_is_local.size() && seq->prop_formal_is_local[i];
    flow.clause = local ? "16.8.2" : "16.10";
    CheckReads(arg, assigned, flow);
    flow.clause = "16.10";
  }
}

void FlowBody(const SeqLinearBody& body, NameSet& assigned, Flow& flow);

void FlowTree(const PropertyExprNode* node, NameSet& assigned, Flow& flow) {
  if (node == nullptr) return;
  if (node->kind != PropertyExprNode::Kind::kAbort) {
    CheckReads(node->boolean, assigned, flow);
  }
  if (node->sequence != nullptr) {
    FlowBody(node->sequence->seq_linear, assigned, flow);
  }
  for (const PropertyExprNode* operand : node->operands) {
    FlowTree(operand, assigned, flow);
  }
}

// The match items written with an operand standing at `loc`, in order: each
// reads its right-hand side, and a compound assignment or an increment or
// decrement reads the local it assigns as well.
void FlowMatchItems(const std::vector<SeqMatchAssign>& items, SourceLoc loc,
                    NameSet& assigned, Flow& flow) {
  for (const SeqMatchAssign& item : items) {
    CheckReads(item.rhs, assigned, flow);
    CheckReads(item.call, assigned, flow);
    if (item.call != nullptr || item.lvar.empty()) continue;
    bool reads = !item.init && item.op != TokenKind::kEq;
    if (reads && flow.tracked.count(item.lvar) != 0 &&
        assigned.count(item.lvar) == 0) {
      flow.found.push_back({item.lvar, loc});
    }
    assigned.insert(item.lvar);
  }
}

bool RepeatedFromZero(const SeqLinearBody& body, size_t i) {
  if (i >= body.repetitions.size()) return false;
  const SeqRepetition& rep = body.repetitions[i];
  return rep.kind != SeqRepetition::Kind::kNone && rep.min_expr == nullptr &&
         rep.min == 0;
}

// The operand `i` of `body` and its match items; an operand repeated from
// zero has a match assigning nothing, so it leaves what was assigned as it
// found it.
void FlowStep(const SeqLinearBody& body, size_t i, NameSet& assigned,
              Flow& flow) {
  NameSet before = assigned;
  const Expr* operand = body.operands[i];
  std::vector<std::string_view> given;
  if (operand != nullptr && operand->property_actual != nullptr) {
    FlowTree(operand->property_actual, assigned, flow);
  } else {
    FlowOperand(operand, assigned, flow, given);
  }
  assigned.insert(given.begin(), given.end());
  if (i < body.match_items.size()) {
    SourceLoc loc = operand != nullptr ? operand->range.start : SourceLoc{};
    FlowMatchItems(body.match_items[i], loc, assigned, flow);
  }
  if (RepeatedFromZero(body, i)) assigned = std::move(before);
}

// §16.10 with Annex F.5.4: the operands of `body` in order; the operands it
// is conjoined or intersected with run from where it starts, and a local
// flows out of a top-level or only where every alternative assigns it.
void FlowBody(const SeqLinearBody& body, NameSet& assigned, Flow& flow) {
  const NameSet kStart = assigned;
  for (size_t i = 0; i < body.operands.size(); ++i) {
    FlowStep(body, i, assigned, flow);
  }
  for (const auto* joined : {&body.conjuncts, &body.intersects}) {
    for (const SeqLinearBody& inner : *joined) {
      NameSet own = kStart;
      FlowBody(inner, own, flow);
      assigned.insert(own.begin(), own.end());
    }
  }
  for (const SeqLinearBody& alternative : body.alternatives) {
    NameSet own = kStart;
    FlowBody(alternative, own, flow);
    std::erase_if(assigned,
                  [&](std::string_view name) { return own.count(name) == 0; });
  }
  // §16.9.8: the match items of first_match run at the end of its match.
  if (!body.first_match_items.empty()) {
    const Expr* first = body.operands.empty() ? nullptr : body.operands[0];
    FlowMatchItems(body.first_match_items,
                   first != nullptr ? first->range.start : SourceLoc{},
                   assigned, flow);
  }
}

// §16.10: the locals of a declaration with no initialization assignment are
// tracked; each initialization assignment reads only an earlier local that
// has one.
NameSet InitialLocals(const std::vector<SeqLocalDecl>& locals, NameSet& tracked,
                      Flow& flow) {
  NameSet assigned;
  for (const SeqLocalDecl& local : locals) tracked.insert(local.name);
  for (const SeqLocalDecl& local : locals) {
    if (local.init == nullptr) continue;
    CheckReads(local.init, assigned, flow);
    assigned.insert(local.name);
  }
  return assigned;
}

void ReportUnassigned(const std::vector<Unassigned>& found, DiagEngine& diag) {
  std::unordered_set<std::string_view> reported;
  for (const Unassigned& ref : found) {
    if (!reported.insert(ref.name).second) continue;
    diag.Error(ref.loc,
               "the local variable '" + std::string(ref.name) +
                   "' is referenced at a point where it is unassigned",
               Subclause(ref.clause));
  }
}

// §16.10 and §16.8.2: every reference in the declaration `decl` to one of
// its local variables, or to an output local variable formal argument, is
// at a point an assignment to it reaches.
void CheckDeclaration(const ModuleItem* decl, const SequenceMap& sequences,
                      DiagEngine& diag) {
  NameSet tracked;
  std::vector<Unassigned> found;
  Flow flow{sequences, tracked, found};
  const std::vector<SeqLocalDecl>& locals =
      decl->kind == ModuleItemKind::kSequenceDecl ? decl->seq_linear.locals
                                                  : decl->prop_locals;
  NameSet assigned = InitialLocals(locals, tracked, flow);
  for (size_t i = 0; i < decl->prop_formals.size(); ++i) {
    if (decl->kind == ModuleItemKind::kSequenceDecl && FormalAssigns(decl, i) &&
        i < decl->prop_formal_is_local.size() &&
        decl->prop_formal_is_local[i]) {
      tracked.insert(decl->prop_formals[i]);
    }
  }
  if (decl->kind == ModuleItemKind::kSequenceDecl) {
    FlowBody(decl->seq_linear, assigned, flow);
  } else {
    FlowTree(decl->prop_body_tree, assigned, flow);
  }
  ReportUnassigned(found, diag);
}

// §16.10, and §16.13.5 for matched: where triggered or matched is applied to
// an instance and a local variable is the entire actual of a formal, the
// sequence references that formal at no point before it assigns it.
void CheckMethodActuals(const Expr* e, const SequenceMap& sequences,
                        const NameSet& locals, DiagEngine& diag) {
  if (e->kind != ExprKind::kMemberAccess || e->rhs == nullptr ||
      (e->rhs->text != "triggered" && e->rhs->text != "matched")) {
    return;
  }
  const ModuleItem* seq = SequenceOf(e, sequences);
  if (seq == nullptr) return;
  for (size_t i = 0; i < e->lhs->args.size() && i < seq->prop_formals.size();
       ++i) {
    const Expr* arg = e->lhs->args[i];
    if (arg == nullptr || arg->kind != ExprKind::kIdentifier ||
        locals.count(arg->text) == 0) {
      continue;
    }
    const NameSet kFormal{seq->prop_formals[i]};
    std::vector<Unassigned> found;
    Flow flow{sequences, kFormal, found};
    NameSet assigned;
    FlowBody(seq->seq_linear, assigned, flow);
    if (found.empty()) continue;
    bool matched = e->rhs->text == "matched";
    diag.Error(e->range.start,
               "'" + std::string(seq->name) + "' references its formal '" +
                   std::string(seq->prop_formals[i]) +
                   "', bound to the local variable '" + std::string(arg->text) +
                   "', before it assigns it",
               Subclause(matched ? "16.13.5" : "16.10"));
  }
}

template <typename Fn>
void ForEachExprIn(const Expr* e, const Fn& fn) {
  if (e == nullptr) return;
  fn(e);
  ForEachExprChild(e, [&](const Expr* child) { ForEachExprIn(child, fn); });
}

void CheckMethodsInBody(const ModuleItem* seq, const SequenceMap& sequences,
                        DiagEngine& diag) {
  NameSet locals;
  for (const SeqLocalDecl& local : seq->seq_linear.locals) {
    locals.insert(local.name);
  }
  locals.insert(seq->prop_seq_assert_vars.begin(),
                seq->prop_seq_assert_vars.end());
  for (const Expr* operand : seq->seq_linear.operands) {
    ForEachExprIn(operand, [&](const Expr* e) {
      CheckMethodActuals(e, sequences, locals, diag);
    });
  }
}

}  // namespace

void ValidateLocalVariableFlow(const ModuleDecl* decl, DiagEngine& diag) {
  const SequenceMap kSequences = NamedDeclsByName(decl, false);
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      CheckDeclaration(item, kSequences, diag);
      CheckMethodsInBody(item, kSequences, diag);
    }
    if (item->kind == ModuleItemKind::kPropertyDecl &&
        item->prop_body_tree != nullptr) {
      CheckDeclaration(item, kSequences, diag);
    }
  }
}

}  // namespace delta
