#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"

namespace delta {

static void BuildMemberName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    if (!expr->scope_prefix.empty()) {
      out += expr->scope_prefix;
      out += ".";
    }
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kSelect && expr->base != nullptr &&
      expr->index != nullptr && expr->index_end == nullptr &&
      expr->index->kind == ExprKind::kIntegerLiteral) {
    BuildMemberName(expr->base, out);
    out += "[" + std::to_string(expr->index->int_val) + "]";
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildMemberName(expr->lhs, out);
    out += ".";
    BuildMemberName(expr->rhs, out);
  }
}

std::string StripRootPrefix(const std::string& name) {
  constexpr std::string_view kPrefix = "$root.";
  if (name.size() > kPrefix.size() &&
      std::string_view(name).substr(0, kPrefix.size()) == kPrefix) {
    auto rest = std::string_view(name).substr(kPrefix.size());
    auto dot = rest.find('.');
    if (dot != std::string_view::npos) return std::string(rest.substr(dot + 1));
    return std::string(rest);
  }
  return name;
}

std::string HierarchicalReferenceName(const Expr* expr) {
  std::string name;
  BuildMemberName(expr, name);
  return StripRootPrefix(name);
}

std::string RootedReferenceKey(const std::string& name) {
  constexpr std::string_view kPrefix = "$root.";
  if (!std::string_view(name).starts_with(kPrefix)) return {};
  return name;
}

std::string RootedReferenceKey(const Expr* expr) {
  std::string name;
  BuildMemberName(expr, name);
  return RootedReferenceKey(name);
}

Net* FindHierarchicalNet(const Expr* expr, SimContext& ctx) {
  std::string name;
  BuildMemberName(expr, name);
  std::string rooted = RootedReferenceKey(name);
  if (!rooted.empty()) {
    if (Net* net = ctx.FindNet(rooted)) return net;
  }
  return ctx.FindNet(StripRootPrefix(name));
}

std::string_view ArrayRootKey(const Expr* base, Arena& arena) {
  if (base != nullptr &&
      (base->kind == ExprKind::kIdentifier ||
       (base->kind == ExprKind::kMemberAccess && !base->is_scope_resolution))) {
    std::string rooted = RootedReferenceKey(base);
    if (!rooted.empty()) return *arena.Create<std::string>(std::move(rooted));
  }
  std::string_view key = ScopedOrBareTargetKey(base, arena);
  if (!key.empty() || base == nullptr ||
      base->kind != ExprKind::kMemberAccess || base->is_scope_resolution) {
    return key;
  }
  return *arena.Create<std::string>(HierarchicalReferenceName(base));
}

}  // namespace delta
