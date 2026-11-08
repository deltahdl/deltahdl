#include "elaborator/covergroup_instance_rules.h"

#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/covergroup_context.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using Covergroups = std::unordered_map<std::string_view, const CovergroupDecl*>;

bool IsNew(const Expr* e) { return e != nullptr && e->text == "new"; }

struct NewCall {
  const Expr* call;
  const CovergroupDecl& cg;
  size_t positional;
  const CovergroupDeclared& is_net;
  DiagEngine& diag;
};

int ActualIndex(const NewCall& nc, size_t i, std::string_view name) {
  if (i < nc.positional) return static_cast<int>(i);
  for (size_t j = 0; j < nc.call->arg_names.size(); ++j) {
    if (nc.call->arg_names[j] == name) {
      return static_cast<int>(nc.positional + j);
    }
  }
  return -1;
}

void CheckActualsBind(const NewCall& nc) {
  if (nc.positional > nc.cg.formals.size()) {
    nc.diag.Error(nc.call->range.start,
                  std::format("new of covergroup '{}' is given {} actuals for "
                              "its {} formals",
                              nc.cg.name, nc.positional, nc.cg.formals.size()),
                  Subclause("19.3"));
  }
  for (std::string_view name : nc.call->arg_names) {
    if (FindCovergroupFormal(nc.cg, name) != nullptr) continue;
    nc.diag.Error(
        nc.call->range.start,
        std::format("covergroup '{}' has no formal '{}'", nc.cg.name, name),
        Subclause("19.3"));
  }
}

bool IsVariableActual(const Expr* e, const CovergroupDeclared& is_net) {
  if (e->kind == ExprKind::kIdentifier) return !is_net(e->text);
  return e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess;
}

void CheckFormal(const NewCall& nc, size_t i) {
  const FunctionArg& formal = nc.cg.formals[i];
  int index = ActualIndex(nc, i, formal.name);
  const Expr* actual =
      index >= 0 ? nc.call->args[static_cast<size_t>(index)] : nullptr;
  if (actual == nullptr) {
    if (formal.default_value != nullptr) return;
    nc.diag.Error(nc.call->range.start,
                  std::format("new of covergroup '{}' gives no actual to "
                              "formal '{}', which has no default",
                              nc.cg.name, formal.name),
                  Subclause("19.3"));
    return;
  }
  if (!IsRefCovergroupFormal(nc.cg, formal.name) ||
      IsVariableActual(actual, nc.is_net)) {
    return;
  }
  nc.diag.Error(actual->range.start,
                std::format("the actual of ref formal '{}' of covergroup '{}' "
                            "is no variable",
                            formal.name, nc.cg.name),
                Subclause("19.3"));
}

bool IsItemName(const CovergroupDecl& cg, std::string_view name) {
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kCoverPoint &&
        CoverpointName(*item.cover_point) == name) {
      return true;
    }
    if (item.kind == CoverageSpecKind::kCoverCross &&
        item.cover_cross->label == name) {
      return true;
    }
  }
  return false;
}

struct ModuleUses {
  const Covergroups& covergroups;
  const Covergroups& instances;
  const CovergroupDeclared& is_net;
  DiagEngine& diag;
};

const CovergroupDecl* InstanceOf(const Expr* e, const ModuleUses& uses) {
  if (e->kind != ExprKind::kIdentifier) return nullptr;
  auto it = uses.instances.find(e->text);
  return it != uses.instances.end() ? it->second : nullptr;
}

void CheckFormalRead(const Expr* e, const ModuleUses& uses) {
  const CovergroupDecl* cg = InstanceOf(e->lhs, uses);
  if (cg == nullptr) return;
  std::string_view name = e->rhs->text;
  if (FindCovergroupFormal(*cg, name) == nullptr || IsItemName(*cg, name)) {
    return;
  }
  uses.diag.Error(e->range.start,
                  std::format("'{}' is a formal of covergroup '{}', which is "
                              "not visible through instance '{}'",
                              name, cg->name, e->lhs->text),
                  Subclause("19.3"));
}

void CheckItemMethod(const Expr* call, const ModuleUses& uses) {
  const Expr* access = call->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->lhs->kind != ExprKind::kMemberAccess) {
    return;
  }
  std::string_view method = access->rhs->text;
  const CovergroupDecl* cg = InstanceOf(access->lhs->lhs, uses);
  if ((method != "sample" && method != "set_inst_name") || cg == nullptr ||
      !IsItemName(*cg, access->lhs->rhs->text)) {
    return;
  }
  uses.diag.Error(call->range.start,
                  std::format("{}() is a method of a covergroup instance, not "
                              "of its coverpoint or cross '{}'",
                              method, access->lhs->rhs->text),
                  Subclause("19.8"));
}

void CheckAccesses(const Expr* e, const ModuleUses& uses) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kMemberAccess) CheckFormalRead(e, uses);
  if (e->kind == ExprKind::kCall) CheckItemMethod(e, uses);
  ForEachExprChild(e, [&](const Expr* child) { CheckAccesses(child, uses); });
}

void CheckNewOf(const CovergroupDecl* cg, const Expr* rhs,
                const ModuleUses& uses) {
  if (cg == nullptr || !IsNew(rhs)) return;
  CheckCovergroupNewActuals(rhs, *cg, uses.is_net, uses.diag);
}

const CovergroupDecl* DeclaredCovergroup(const Stmt* s,
                                         const ModuleUses& uses) {
  auto it = uses.covergroups.find(s->var_decl_type.type_name);
  return it != uses.covergroups.end() ? it->second : nullptr;
}

void CheckStmt(const Stmt* s, const ModuleUses& uses) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckNewOf(InstanceOf(s->lhs, uses), s->rhs, uses);
  } else if (s->kind == StmtKind::kVarDecl) {
    CheckNewOf(DeclaredCovergroup(s, uses), s->var_init, uses);
  }
  ForEachChildExpr(s, [&](const Expr* e) { CheckAccesses(e, uses); });
  ForEachChildStmt(s, [&](const Stmt* sub) { CheckStmt(sub, uses); });
}

Covergroups CovergroupsOf(const ModuleDecl* decl) {
  Covergroups covergroups;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) {
      covergroups.emplace(item->name, item->covergroup);
    }
  }
  return covergroups;
}

Covergroups InstancesOf(const ModuleDecl* decl,
                        const Covergroups& covergroups) {
  Covergroups instances;
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    auto it = covergroups.find(item->data_type.type_name);
    if (it != covergroups.end()) instances.emplace(item->name, it->second);
  }
  return instances;
}

}  // namespace

void CheckCovergroupNewActuals(const Expr* call, const CovergroupDecl& cg,
                               const CovergroupDeclared& is_net,
                               DiagEngine& diag) {
  const NewCall kNew{call, cg, call->args.size() - call->arg_names.size(),
                     is_net, diag};
  CheckActualsBind(kNew);
  for (size_t i = 0; i < cg.formals.size(); ++i) CheckFormal(kNew, i);
}

void CheckModuleCovergroupInstances(const ModuleDecl* decl, DiagEngine& diag) {
  Covergroups covergroups = CovergroupsOf(decl);
  if (covergroups.empty()) return;
  Covergroups instances = InstancesOf(decl, covergroups);
  std::unordered_set<std::string_view> nets;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kNetDecl) nets.insert(item->name);
  }
  const CovergroupDeclared kIsNet = [&](std::string_view name) {
    return nets.contains(name);
  };
  const ModuleUses kUses{covergroups, instances, kIsNet, diag};
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl) {
      auto it = instances.find(item->name);
      if (it != instances.end()) CheckNewOf(it->second, item->init_expr, kUses);
    } else if (item->kind == ModuleItemKind::kContAssign) {
      CheckAccesses(item->assign_rhs, kUses);
    }
  }
  ForEachBodyOwningItem(decl->items, [&](const auto* body_item) {
    CheckStmt(body_item->body, kUses);
    for (const Stmt* s : body_item->func_body_stmts) CheckStmt(s, kUses);
  });
}

}  // namespace delta
