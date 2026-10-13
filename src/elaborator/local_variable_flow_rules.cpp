#include <algorithm>
#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/assertion_walk.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using NameSet = std::unordered_set<std::string_view>;

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
  const NamedDecls& sequences;
  const NameSet& tracked;
  std::vector<Unassigned>& found;
  // The clause a reference found now is reported under: §16.8.2 for the
  // actual of an input or inout local variable formal argument.
  const char* clause = "16.10";
};

void CheckReads(const Expr* e, const NameSet& assigned, Flow& flow) {
  ForEachSubExpr(e, [&](const Expr* sub) {
    if (IsLocalRef(sub, flow.tracked) && assigned.count(sub->text) == 0) {
      flow.found.push_back({sub->text, sub->range.start, flow.clause});
    }
  });
}

// The call of the named sequence `e` instantiates, written with an argument
// list, or that triggered or matched is applied to; null where it is none.
const Expr* SequenceCall(const Expr* e, const NamedDecls& sequences) {
  const Expr* call = SequenceMethodOf(e).empty() ? e : e->lhs;
  return call->kind == ExprKind::kCall &&
                 InstantiatedDecl(call, sequences) != nullptr
             ? call
             : nullptr;
}

// §16.8.2 and §16.10: whether the formal `i` of `seq` gives the local
// variable bound to it a value rather than reading it: an output local
// variable formal argument, or an untyped formal the body assigns.
bool FormalAssigns(const ModuleItem* seq, size_t i) {
  if (seq->prop_formal_is_local[i]) {
    return LocalFormalDirections(seq)[i] == Direction::kOutput;
  }
  return BodyAssigns(seq->seq_linear, seq->prop_formals[i]);
}

// An operand of a body: an instance's actuals are read, but for a local
// bound whole to a formal that gives it a value, which is assigned after the
// operand.
void FlowOperand(const Expr* operand, NameSet& assigned, Flow& flow,
                 std::vector<std::string_view>& given) {
  const Expr* call = SequenceCall(operand, flow.sequences);
  if (call == nullptr) {
    CheckReads(operand, assigned, flow);
    return;
  }
  const ModuleItem* seq = InstantiatedDecl(call, flow.sequences);
  size_t written = std::min(call->args.size(), seq->prop_formals.size());
  for (size_t i = 0; i < written; ++i) {
    const Expr* arg = call->args[i];
    if (IsLocalRef(arg, flow.tracked) && FormalAssigns(seq, i)) {
      given.push_back(arg->text);
      continue;
    }
    flow.clause = seq->prop_formal_is_local[i] ? "16.8.2" : "16.10";
    CheckReads(arg, assigned, flow);
    flow.clause = "16.10";
  }
}

void FlowBody(const SeqLinearBody& body, NameSet& assigned, Flow& flow);

void FlowTree(const PropertyExprNode* node, NameSet& assigned, Flow& flow) {
  ForEachTreeNode(node, [&](const PropertyExprNode& n) {
    if (n.kind != PropertyExprNode::Kind::kAbort) {
      CheckReads(n.boolean, assigned, flow);
    }
    if (n.sequence != nullptr) FlowBody(n.sequence->seq_linear, assigned, flow);
  });
}

// The match items written with an operand standing at `loc`, in order: each
// reads its right-hand side, and a compound assignment or an increment or
// decrement reads the local it assigns as well.
void FlowMatchItems(const std::vector<SeqMatchAssign>& items, SourceLoc loc,
                    NameSet& assigned, Flow& flow) {
  for (const SeqMatchAssign& item : items) {
    CheckReads(item.rhs, assigned, flow);
    CheckReads(item.call, assigned, flow);
    if (item.call != nullptr) continue;
    if (item.op != TokenKind::kEq && flow.tracked.count(item.lvar) != 0 &&
        assigned.count(item.lvar) == 0) {
      flow.found.push_back({item.lvar, loc});
    }
    assigned.insert(item.lvar);
  }
}

// The operand `i` of `body` and its match items; an operand repeated from
// zero has a match assigning nothing, so it leaves what was assigned as it
// found it.
void FlowStep(const SeqLinearBody& body, size_t i, NameSet& assigned,
              Flow& flow) {
  NameSet before = assigned;
  const Expr* operand = body.operands[i];
  std::vector<std::string_view> given;
  if (operand->property_actual != nullptr) {
    FlowTree(operand->property_actual, assigned, flow);
  } else {
    FlowOperand(operand, assigned, flow, given);
  }
  assigned.insert(given.begin(), given.end());
  FlowMatchItems(body.match_items[i], operand->range.start, assigned, flow);
  if (RepeatedFromZero(body, i)) assigned = std::move(before);
}

// §16.10 with Annex F.5.4: the operands of `body` in order, a throughout's
// condition read where its operands begin; the operands it is conjoined or
// intersected with run from where it starts, a local flows
// out of a top-level or only where every alternative assigns it, and the
// match items of first_match run at the end of its match.
void FlowBody(const SeqLinearBody& body, NameSet& assigned, Flow& flow) {
  const NameSet kStart = assigned;
  for (size_t i = 0; i < body.operands.size(); ++i) {
    // §16.9.9: a throughout's condition holds at every tick of the
    // operands it governs, so reads what is assigned where they begin.
    for (const SeqThroughout& guard : body.throughouts) {
      if (guard.first == i) CheckReads(guard.cond, assigned, flow);
    }
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
  if (!body.first_match_items.empty()) {
    FlowMatchItems(body.first_match_items, body.operands[0]->range.start,
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
  for (const Unassigned& ref : found) {
    diag.Error(ref.loc,
               "the local variable '" + std::string(ref.name) +
                   "' is referenced at a point where it is unassigned",
               Subclause(ref.clause));
  }
}

// §16.10 and §16.8.2: every reference in the declaration `decl` to one of
// its local variables, or to an output local variable formal argument, is
// at a point an assignment to it reaches.
void CheckDeclaration(const ModuleItem* decl, const NamedDecls& sequences,
                      DiagEngine& diag) {
  NameSet tracked;
  std::vector<Unassigned> found;
  Flow flow{sequences, tracked, found};
  bool sequence = decl->kind == ModuleItemKind::kSequenceDecl;
  NameSet assigned = InitialLocals(
      sequence ? decl->seq_linear.locals : decl->prop_locals, tracked, flow);
  std::vector<Direction> dirs = LocalFormalDirections(decl);
  for (size_t i = 0; i < dirs.size(); ++i) {
    if (dirs[i] == Direction::kOutput) tracked.insert(decl->prop_formals[i]);
  }
  FlowBody(decl->seq_linear, assigned, flow);
  FlowTree(decl->prop_body_tree, assigned, flow);
  ReportUnassigned(found, diag);
}

// §16.10, and §16.13.5 for matched: where triggered or matched is applied to
// an instance and a local variable is the entire actual of a formal, the
// sequence references that formal at no point before it assigns it.
void CheckMethodActuals(const Expr* e, const NamedDecls& sequences,
                        const NameSet& locals, DiagEngine& diag) {
  std::string_view method = SequenceMethodOf(e);
  const Expr* call = method.empty() ? nullptr : SequenceCall(e, sequences);
  if (call == nullptr) return;
  const ModuleItem* seq = InstantiatedDecl(call, sequences);
  size_t written = std::min(call->args.size(), seq->prop_formals.size());
  for (size_t i = 0; i < written; ++i) {
    if (!IsLocalRef(call->args[i], locals)) continue;
    const NameSet kFormal{seq->prop_formals[i]};
    std::vector<Unassigned> found;
    Flow flow{sequences, kFormal, found};
    NameSet assigned;
    FlowBody(seq->seq_linear, assigned, flow);
    if (found.empty()) continue;
    diag.Error(e->range.start,
               "'" + std::string(seq->name) + "' references its formal '" +
                   std::string(seq->prop_formals[i]) +
                   "', bound to the local variable '" +
                   std::string(call->args[i]->text) + "', before it assigns it",
               Subclause(method == "matched" ? "16.13.5" : "16.10"));
  }
}

void CheckMethodsInBody(const ModuleItem* seq, const NamedDecls& sequences,
                        DiagEngine& diag) {
  NameSet locals(seq->prop_seq_assert_vars.begin(),
                 seq->prop_seq_assert_vars.end());
  for (const SeqLocalDecl& local : seq->seq_linear.locals) {
    locals.insert(local.name);
  }
  ForEachBodyExpr(seq->seq_linear, [&](const Expr* operand) {
    ForEachSubExpr(operand, [&](const Expr* e) {
      CheckMethodActuals(e, sequences, locals, diag);
    });
  });
}

}  // namespace

void ValidateLocalVariableFlow(const ModuleDecl* decl, DiagEngine& diag) {
  const NamedDecls kSequences = NamedDeclsByName(decl, false);
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      CheckMethodsInBody(item, kSequences, diag);
    }
    if (item->kind == ModuleItemKind::kSequenceDecl ||
        item->kind == ModuleItemKind::kPropertyDecl) {
      CheckDeclaration(item, kSequences, diag);
    }
  }
}

}  // namespace delta
