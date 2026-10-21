#include "elaborator/assertion_walk.h"

#include <cstddef>
#include <functional>
#include <initializer_list>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

void ForEachProceduralStmt(const ModuleItem* item,
                           const std::function<void(const Stmt*)>& fn) {
  std::function<void(const Stmt*)> visit = [&](const Stmt* s) {
    if (s == nullptr) return;
    fn(s);
    ForEachChildStmt(s, [&](Stmt* const& sub) { visit(sub); });
  };
  for (const Stmt* s : item->func_body_stmts) visit(s);
  if (IsProceduralItemKind(item->kind)) visit(item->body);
}

void ForEachConcurrentAssertion(const ModuleDecl* decl,
                                const std::function<void(const Stmt*)>& fn) {
  for (const ModuleItem* item : decl->items) {
    if (item->body != nullptr && item->body->is_concurrent_clocked &&
        !IsProceduralItemKind(item->kind)) {
      fn(item->body);
    }
    ForEachProceduralStmt(item, [&](const Stmt* s) {
      if (s->is_procedural_concurrent) fn(s);
    });
  }
}

NamedDecls NamedDeclsByName(const ModuleDecl* decl, bool with_properties) {
  NamedDecls named;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl ||
        (with_properties && item->kind == ModuleItemKind::kPropertyDecl)) {
      named[item->name] = item;
    }
  }
  return named;
}

void ForEachSubExpr(const Expr* e, const std::function<void(const Expr*)>& fn) {
  if (e == nullptr) return;
  fn(e);
  ForEachExprChild(e, [&](const Expr* child) { ForEachSubExpr(child, fn); });
}

bool AnySubExpr(const Expr* e, const std::function<bool(const Expr*)>& pred) {
  if (e == nullptr) return false;
  return pred(e) || AnyExprChild(e, [&](const Expr* child) {
           return AnySubExpr(child, pred);
         });
}

void ForEachBody(const SeqLinearBody& body,
                 const std::function<void(const SeqLinearBody&)>& fn) {
  fn(body);
  for (const auto* nested :
       {&body.intersects, &body.conjuncts, &body.alternatives}) {
    for (const SeqLinearBody& inner : *nested) ForEachBody(inner, fn);
  }
}

void ForEachBodyExpr(const SeqLinearBody& body,
                     const std::function<void(const Expr*)>& fn) {
  ForEachBody(body, [&](const SeqLinearBody& b) {
    for (const Expr* operand : b.operands) fn(operand);
    for (const auto& items : b.match_items) {
      for (const SeqMatchAssign& item : items) {
        fn(item.rhs);
        fn(item.call);
      }
    }
    for (const SeqMatchAssign& item : b.first_match_items) {
      fn(item.rhs);
      fn(item.call);
    }
    for (const SeqThroughout& guard : b.throughouts) fn(guard.cond);
  });
}

void ForEachTreeNode(const PropertyExprNode* node,
                     const std::function<void(const PropertyExprNode&)>& fn) {
  if (node == nullptr) return;
  fn(*node);
  for (const PropertyExprNode* operand : node->operands) {
    ForEachTreeNode(operand, fn);
  }
}

void ForEachTreeExpr(const PropertyExprNode* node,
                     const std::function<void(const Expr*)>& fn) {
  ForEachTreeNode(node, [&](const PropertyExprNode& n) {
    fn(n.boolean);
    if (n.sequence != nullptr) ForEachBodyExpr(n.sequence->seq_linear, fn);
  });
}

bool TreeNamesClocks(const PropertyExprNode* node) {
  bool named = false;
  ForEachTreeNode(node, [&named](const PropertyExprNode& n) {
    named = named || !n.clock.empty();
    if (n.sequence == nullptr) return;
    ForEachBody(n.sequence->seq_linear, [&named](const SeqLinearBody& b) {
      for (const auto& clock : b.clocks) named = named || !clock.empty();
    });
  });
  return named;
}

const ModuleItem* InstantiatedDecl(const Expr* e, const NamedDecls& decls) {
  std::string_view name = e->kind == ExprKind::kCall ? e->callee : e->text;
  auto it = decls.find(name);
  return it == decls.end() ? nullptr : it->second;
}

bool IsNameRef(const Expr* e, std::string_view name) {
  return e != nullptr && e->kind == ExprKind::kIdentifier && e->text == name;
}

bool IsLocalRef(const Expr* e,
                const std::unordered_set<std::string_view>& locals) {
  return e != nullptr && e->kind == ExprKind::kIdentifier &&
         locals.count(e->text) != 0;
}

bool RepeatedFromZero(const SeqLinearBody& body, size_t i) {
  const SeqRepetition& rep = body.repetitions[i];
  return rep.kind != SeqRepetition::Kind::kNone && rep.min_expr == nullptr &&
         rep.min == 0;
}

std::string_view SequenceMethodOf(const Expr* e) {
  if (e->kind != ExprKind::kMemberAccess) return {};
  std::string_view method = e->rhs->text;
  return method == "triggered" || method == "matched" ? method : "";
}

std::vector<Direction> LocalFormalDirections(const ModuleItem* seq) {
  std::vector<Direction> dirs(seq->prop_formals.size(), Direction::kNone);
  auto next = seq->prop_seq_local_lvar_directions.begin();
  for (size_t i = 0; i < dirs.size(); ++i) {
    if (!seq->prop_formal_is_local[i]) continue;
    bool written = next != seq->prop_seq_local_lvar_directions.end();
    dirs[i] = written ? *next++ : Direction::kInput;
  }
  return dirs;
}

bool EventsMention(const std::vector<EventExpr>& events,
                   const std::unordered_set<std::string_view>& names) {
  for (const EventExpr& ev : events) {
    if (ExprMentionsAny(ev.signal, names) ||
        ExprMentionsAny(ev.iff_condition, names)) {
      return true;
    }
  }
  return false;
}

bool IsOutward(Direction dir) {
  return dir == Direction::kInout || dir == Direction::kOutput;
}

bool ItemsAssign(const std::vector<SeqMatchAssign>& items,
                 std::string_view name) {
  for (const SeqMatchAssign& item : items) {
    if (item.lvar == name) return true;
  }
  return false;
}

bool BodyAssigns(const SeqLinearBody& body, std::string_view name) {
  bool assigns = false;
  ForEachBody(body, [&](const SeqLinearBody& b) {
    if (ItemsAssign(b.first_match_items, name)) assigns = true;
    for (const auto& items : b.match_items) {
      if (ItemsAssign(items, name)) assigns = true;
    }
  });
  return assigns;
}

void CountFormalInExpr(const Expr* e, std::string_view name,
                       FormalReferences& refs) {
  ForEachSubExpr(e, [&](const Expr* sub) {
    refs.all += static_cast<int>(IsNameRef(sub, name));
    if (sub->kind != ExprKind::kCall) return;
    for (const Expr* arg : sub->args) {
      refs.permitted += static_cast<int>(IsNameRef(arg, name));
    }
  });
}

namespace {

void CountFormalInBounds(const SeqCycleDelay& bounds, std::string_view name,
                         FormalReferences& refs) {
  CountFormalInExpr(bounds.min_expr, name, refs);
  if (bounds.max_expr == bounds.min_expr) return;
  CountFormalInExpr(bounds.max_expr, name, refs);
  refs.permitted += static_cast<int>(IsNameRef(bounds.max_expr, name));
}

}  // namespace

void CountFormalInBody(const SeqLinearBody& body, std::string_view name,
                       FormalReferences& refs) {
  ForEachBody(body, [&](const SeqLinearBody& b) {
    for (const SeqCycleDelay& delay : b.delays) {
      CountFormalInBounds(delay, name, refs);
    }
    for (const SeqRepetition& rep : b.repetitions) {
      CountFormalInBounds(rep, name, refs);
    }
  });
  ForEachBodyExpr(body,
                  [&](const Expr* e) { CountFormalInExpr(e, name, refs); });
}

void CountFormalInTree(const PropertyExprNode* node, std::string_view name,
                       FormalReferences& refs) {
  ForEachTreeNode(node, [&](const PropertyExprNode& n) {
    CountFormalInExpr(n.boolean, name, refs);
    CountFormalInExpr(n.range_min, name, refs);
    CountFormalInExpr(n.range_max, name, refs);
    if (n.sequence != nullptr) {
      CountFormalInBody(n.sequence->seq_linear, name, refs);
    }
  });
}

}  // namespace delta
