#include "elaborator/local_variable_paths.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <initializer_list>
#include <optional>
#include <span>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/specparam_paths.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

enum class LocalReach : uint8_t {
  kNoLocal,
  kStaticLocal,
  kAutomaticLocal,
  kUnnamedBlockLocal
};

struct LocalScope {
  std::vector<const Stmt*> children;
  std::span<const FunctionArg> args;
  bool automatic_by_default = false;
};

bool IsBlock(const Stmt* s) {
  return s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork;
}

bool IsNamedBlock(const Stmt* s) { return IsBlock(s) && !s->label.empty(); }

std::vector<const Stmt*> ChildrenOf(const Stmt* s) {
  std::vector<const Stmt*> children;
  ForEachChildStmt(s, [&](const Stmt* sub) {
    if (sub != nullptr) children.push_back(sub);
  });
  return children;
}

const Stmt* NamedBlockUnder(const Stmt* s, std::string_view name) {
  if (IsNamedBlock(s)) return s->label == name ? s : nullptr;
  const Stmt* found = nullptr;
  ForEachChildStmt(s, [&](const Stmt* sub) {
    if (found == nullptr && sub != nullptr) found = NamedBlockUnder(sub, name);
  });
  return found;
}

const Stmt* NamedBlockAmong(const std::vector<const Stmt*>& stmts,
                            std::string_view name) {
  for (const Stmt* s : stmts) {
    if (const Stmt* found = NamedBlockUnder(s, name)) return found;
  }
  return nullptr;
}

bool DeclaredInAnUnnamedBlock(const Stmt* s, std::string_view name,
                              bool inside_unnamed) {
  if (s->kind == StmtKind::kVarDecl) {
    return inside_unnamed && s->var_name == name;
  }
  const bool kInside = inside_unnamed || IsBlock(s);
  bool found = false;
  ForEachChildStmt(s, [&](const Stmt* sub) {
    if (!found && sub != nullptr && !IsNamedBlock(sub)) {
      found = DeclaredInAnUnnamedBlock(sub, name, kInside);
    }
  });
  return found;
}

LocalReach LifetimeReach(bool automatic) {
  return automatic ? LocalReach::kAutomaticLocal : LocalReach::kStaticLocal;
}

LocalReach ReachOfVariable(const LocalScope& scope, std::string_view name) {
  if (std::ranges::any_of(scope.args, [name](const FunctionArg& arg) {
        return arg.name == name;
      })) {
    return LifetimeReach(scope.automatic_by_default);
  }
  for (const Stmt* s : scope.children) {
    if (s->kind == StmtKind::kVarDecl && s->var_name == name) {
      return LifetimeReach(scope.automatic_by_default ? !s->var_is_static
                                                      : s->var_is_automatic);
    }
  }
  const bool kInUnnamed =
      std::ranges::any_of(scope.children, [name](const Stmt* s) {
        return !IsNamedBlock(s) && DeclaredInAnUnnamedBlock(s, name, false);
      });
  return kInUnnamed ? LocalReach::kUnnamedBlockLocal : LocalReach::kNoLocal;
}

bool IsSubroutine(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kTaskDecl;
}

std::optional<LocalScope> RootScope(const ModuleDecl& decl,
                                    std::string_view root) {
  for (const ModuleItem* item : decl.items) {
    if (IsSubroutine(item) && item->name == root) {
      return LocalScope{
          std::vector<const Stmt*>(item->func_body_stmts.begin(),
                                   item->func_body_stmts.end()),
          item->func_args,
          item->is_automatic || (decl.is_automatic && !item->is_static)};
    }
    if (!IsProceduralItemKind(item->kind) || item->body == nullptr) continue;
    if (const Stmt* block = NamedBlockUnder(item->body, root)) {
      return LocalScope{ChildrenOf(block), {}, false};
    }
  }
  return std::nullopt;
}

LocalReach ReachOfPath(const ModuleDecl& decl, const InstancePath& path,
                       std::string_view& variable) {
  std::optional<LocalScope> scope = RootScope(decl, path.front());
  if (!scope) return LocalReach::kNoLocal;
  for (std::size_t i = 1; i < path.size(); ++i) {
    if (const Stmt* block = NamedBlockAmong(scope->children, path[i])) {
      scope->children = ChildrenOf(block);
      scope->args = {};
      continue;
    }
    variable = path[i];
    return ReachOfVariable(*scope, path[i]);
  }
  return LocalReach::kNoLocal;
}

class PathCheck {
 public:
  PathCheck(const ModuleDecl& decl, DiagEngine& diag)
      : decl_(decl), diag_(diag) {}

  void operator()(const Expr* e) const {
    if (e->kind != ExprKind::kMemberAccess) return;
    const InstancePath kPath = InstancePathOf(*e);
    if (kPath.empty()) return;
    std::string_view variable;
    const LocalReach kReach = ReachOfPath(decl_, kPath, variable);
    if (kReach == LocalReach::kAutomaticLocal) {
      diag_.ErrorOnce(e->range.start,
                      std::format("hierarchical name reaches automatic "
                                  "variable '{}'",
                                  variable),
                      Subclause("6.21"));
    } else if (kReach == LocalReach::kUnnamedBlockLocal) {
      diag_.ErrorOnce(e->range.start,
                      std::format("hierarchical name reaches variable '{}' "
                                  "declared in an unnamed block",
                                  variable),
                      Subclause("6.21"));
    }
  }

 private:
  const ModuleDecl& decl_;
  DiagEngine& diag_;
};

void CheckStmt(const Stmt* s, const PathCheck& check) {
  if (s == nullptr) return;
  ForEachChildExpr(s, [&](const Expr* e) { ForEachExprUnder(e, check); });
  ForEachChildStmt(s, [&](const Stmt* sub) { CheckStmt(sub, check); });
}

}  // namespace

void ReportPathsToUnreachableLocals(const ModuleDecl& decl, DiagEngine& diag) {
  const PathCheck kCheck(decl, diag);
  for (const ModuleItem* item : decl.items) {
    for (const Expr* e :
         {item->init_expr, item->assign_lhs, item->assign_rhs}) {
      ForEachExprUnder(e, kCheck);
    }
    CheckStmt(item->body, kCheck);
    for (const Stmt* s : item->func_body_stmts) CheckStmt(s, kCheck);
  }
}

}  // namespace delta
