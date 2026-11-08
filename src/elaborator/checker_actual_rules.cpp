#include "elaborator/checker_actual_rules.h"

#include <algorithm>
#include <cstddef>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/checker_procedure_rules.h"
#include "elaborator/net_data_type.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using NameSet = std::unordered_set<std::string_view>;

bool Mentions(const Expr* e, std::string_view name) {
  return AnySubExpr(e, [&](const Expr* sub) { return IsNameRef(sub, name); });
}

const Expr* ActualFor(const ModuleItem* item, const ModuleDecl* decl,
                      size_t i) {
  const PortDecl& port = decl->ports[i];
  for (size_t k = 0; k < item->inst_ports.size(); ++k) {
    const auto& [name, actual] = item->inst_ports[k];
    if (name == port.name || (name.empty() && k == i)) return actual;
  }
  return port.default_value;
}

bool IsLvalue(const Expr* e) {
  if (e->kind == ExprKind::kConcatenation) {
    return std::ranges::all_of(e->elements, IsLvalue);
  }
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kSelect ||
         e->kind == ExprKind::kMemberAccess;
}

void ForEachProceduralOrAssignExpr(const ModuleDecl* decl,
                                   const std::function<void(const Expr*)>& fn) {
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      fn(item->assign_lhs);
      fn(item->assign_rhs);
    }
    if (IsProceduralItemKind(item->kind)) ForEachStmtReadExpr(item->body, fn);
  }
}

FormalReferences CheckerReferences(const ModuleDecl* decl,
                                   std::string_view name) {
  FormalReferences refs;
  ForEachConcurrentAssertion(decl, [&](const Stmt* s) {
    CountFormalInExpr(s->assert_expr, name, refs);
    CountFormalInTree(s->assert_property, name, refs);
  });
  for (const ModuleItem* item : decl->items) {
    CountFormalInBody(item->seq_linear, name, refs);
    CountFormalInExpr(item->prop_body_expr, name, refs);
    CountFormalInTree(item->prop_body_tree, name, refs);
    for (const auto& [port, actual] : item->inst_ports) {
      refs.all += static_cast<int>(Mentions(actual, name));
      refs.permitted += static_cast<int>(IsNameRef(actual, name));
    }
    const ModuleDecl* nested = item->nested_module_decl;
    if (nested == nullptr) continue;
    for (const PortDecl& port : nested->ports) {
      refs.all += static_cast<int>(Mentions(port.default_value, name));
      refs.permitted += static_cast<int>(IsNameRef(port.default_value, name));
    }
  }
  ForEachProceduralOrAssignExpr(decl, [&](const Expr* e) {
    refs.all += static_cast<int>(Mentions(e, name));
  });
  return refs;
}

void CheckDollarActual(const ModuleItem* item, const ModuleDecl* checker,
                       size_t i, DiagEngine& diag) {
  if (CheckerFormalAdmitsDollar(checker, i)) return;
  const PortDecl& port = checker->ports[i];
  diag.Error(item->loc,
             "$ binds the formal '" + std::string(port.name) +
                 "' of checker '" + std::string(checker->name) +
                 "', which shall be untyped and referenced only as the upper "
                 "bound of a cycle delay range, as an actual argument of an "
                 "instance or as a nested checker's default",
             Subclause("17.3"));
}

bool IsConstCast(const Expr* e) {
  return e->kind == ExprKind::kCast && e->text == "const";
}

bool CovergroupReferences(const ModuleDecl* decl, std::string_view name) {
  std::vector<const Expr*> exprs;
  for (const ModuleItem* item : decl->items) {
    const CovergroupDecl* cg = item->covergroup;
    if (cg == nullptr) continue;
    for (const EventExpr& ev : cg->event.clocking) exprs.push_back(ev.signal);
    for (const CoverageSpecOrOption& spec : cg->items) {
      if (spec.cover_point == nullptr) continue;
      exprs.push_back(spec.cover_point->expr);
      exprs.push_back(spec.cover_point->iff);
    }
  }
  return std::ranges::any_of(exprs,
                             [&](const Expr* e) { return Mentions(e, name); });
}

void CheckTaintedFormalUse(const ModuleItem* item, const ModuleDecl* checker,
                           size_t i, std::string_view why, DiagEngine& diag) {
  std::string_view name = checker->ports[i].name;
  bool used = false;
  ForEachProceduralOrAssignExpr(checker, [&](const Expr* e) {
    if (Mentions(e, name)) used = true;
  });
  if (!used) return;
  diag.Error(item->loc,
             "the formal '" + std::string(name) + "' of checker '" +
                 std::string(checker->name) + "', bound to " +
                 std::string(why) +
                 ", is used in a continuous assignment or procedural code",
             Subclause("17.3"));
}

bool IsDynamicVariable(const ModuleItem* item, const TypeShapeTables& tables) {
  std::vector<std::string_view> names;
  FollowTypedefs(item->data_type, tables.typedefs, names);
  bool handle = std::ranges::any_of(names, [&](std::string_view name) {
    return tables.class_names.contains(name);
  });
  return handle || !TypedefDimsAreFixedSize(item->data_type, tables) ||
         std::ranges::any_of(item->unpacked_dims, [&](const Expr* d) {
           return !IsFixedSizeUnpackedDim(d, tables);
         });
}

void ForEachCheckerExpr(const ModuleDecl* decl,
                        const std::function<void(const Expr*)>& fn) {
  ForEachConcurrentAssertion(decl, [&](const Stmt* s) {
    fn(s->assert_expr);
    ForEachTreeExpr(s->assert_property, fn);
  });
  for (const ModuleItem* item : decl->items) {
    ForEachBodyExpr(item->seq_linear, fn);
    fn(item->prop_body_expr);
    ForEachTreeExpr(item->prop_body_tree, fn);
  }
  ForEachProceduralOrAssignExpr(decl, fn);
}

void CheckEnclosingRefs(const ModuleDecl* checker, NameSet dynamic,
                        NameSet forks, DiagEngine& diag) {
  for (const PortDecl& port : checker->ports) {
    dynamic.erase(port.name);
    forks.erase(port.name);
  }
  for (const ModuleItem* item : checker->items) {
    dynamic.erase(item->name);
    forks.erase(item->name);
  }
  ForEachCheckerExpr(checker, [&](const Expr* root) {
    ForEachSubExpr(root, [&](const Expr* e) {
      const Expr* base = e->kind == ExprKind::kSelect ? e->base : e->lhs;
      bool access =
          e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess;
      if (access && IsLocalRef(base, dynamic)) {
        diag.Error(e->range.start,
                   "checker '" + std::string(checker->name) +
                       "' references a member or element of the dynamic "
                       "variable '" +
                       std::string(base->text) + "' of its enclosing scope",
                   Subclause("17.2"));
      }
      if (e->kind == ExprKind::kMemberAccess && IsLocalRef(base, forks)) {
        diag.Error(e->range.start,
                   "checker '" + std::string(checker->name) +
                       "' references an element of the fork-join block '" +
                       std::string(base->text) + "' of its enclosing scope",
                   Subclause("17.2"));
      }
    });
  });
}

void CheckOutsideFunctionCalls(const ModuleDecl* checker, NamedDecls funcs,
                               DiagEngine& diag) {
  for (const ModuleItem* item : checker->items) funcs.erase(item->name);
  auto check = [&](const Expr* e) {
    if (e->kind != ExprKind::kCall) return;
    auto it = funcs.find(e->callee);
    if (it == funcs.end()) return;
    if (!HasArgumentWrittenBack(it->second) && !FunctionIsImpure(it->second)) {
      return;
    }
    diag.Error(e->range.start,
               "function '" + std::string(e->callee) +
                   "' writes an argument back, keeps state or has a side "
                   "effect and cannot be called on the right-hand side of a "
                   "checker variable assignment",
               Subclause("17.8"));
  };
  for (const ModuleItem* item : checker->items) {
    ForEachProceduralStmt(item, [&](const Stmt* s) {
      if (s->kind == StmtKind::kBlockingAssign ||
          s->kind == StmtKind::kNonblockingAssign) {
        ForEachSubExpr(s->rhs, check);
      }
    });
  }
}

}  // namespace

bool CheckerFormalAdmitsDollar(const ModuleDecl* checker, size_t i) {
  const PortDecl& port = checker->ports[i];
  FormalReferences refs = CheckerReferences(checker, port.name);
  return port.formal_type == PropertyFormalType::kUntyped &&
         refs.all == refs.permitted;
}

void ValidateCheckerActuals(const ModuleItem* item, const ModuleDecl* checker,
                            DiagEngine& diag) {
  for (size_t i = 0; i < checker->ports.size(); ++i) {
    const PortDecl& port = checker->ports[i];
    const Expr* actual = ActualFor(item, checker, i);
    if (actual == nullptr) continue;
    if (port.direction == Direction::kOutput && !IsLvalue(actual)) {
      diag.Error(actual->range.start,
                 "the output actual of the formal '" + std::string(port.name) +
                     "' of checker '" + std::string(checker->name) +
                     "' is neither a variable nor a net lvalue",
                 Subclause("17.3"));
    }
    if (IsNameRef(actual, "$")) CheckDollarActual(item, checker, i, diag);
    if (!AnySubExpr(actual, IsConstCast)) continue;
    CheckTaintedFormalUse(item, checker, i, "a const cast", diag);
    if (CovergroupReferences(checker, port.name)) {
      diag.Error(actual->range.start,
                 "the formal '" + std::string(port.name) + "' of checker '" +
                     std::string(checker->name) +
                     "', which a covergroup references, has a const actual",
                 Subclause("17.6"));
    }
  }
}

void ValidateProceduralCheckerActuals(
    const ModuleItem* item, const ModuleDecl* checker,
    const std::unordered_set<std::string_view>& automatics, DiagEngine& diag) {
  for (size_t i = 0; i < checker->ports.size(); ++i) {
    const Expr* actual = ActualFor(item, checker, i);
    bool automatic = AnySubExpr(
        actual, [&](const Expr* sub) { return IsLocalRef(sub, automatics); });
    if (automatic) {
      CheckTaintedFormalUse(item, checker, i, "an automatic value", diag);
    }
  }
}

void ValidateCheckerEnclosingRefs(const ModuleDecl* decl,
                                  const TypeShapeTables& tables,
                                  const NamedDecls& funcs, DiagEngine& diag) {
  NameSet dynamic;
  NameSet forks;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl &&
        IsDynamicVariable(item, tables)) {
      dynamic.insert(item->name);
    }
    ForEachProceduralStmt(item, [&](const Stmt* s) {
      if (s->kind == StmtKind::kFork && !s->label.empty()) {
        forks.insert(s->label);
      }
    });
  }
  for (const ModuleItem* item : decl->items) {
    const ModuleDecl* nested = item->nested_module_decl;
    if (nested == nullptr || nested->decl_kind != ModuleDeclKind::kChecker) {
      continue;
    }
    CheckEnclosingRefs(nested, dynamic, forks, diag);
    CheckOutsideFunctionCalls(nested, funcs, diag);
  }
}

}  // namespace delta
