// §23.6: the flattened name a hierarchical reference is read by. A dotted
// name, `s.y` or `$root.t.s.y`, is spelled out from its parts, and the
// `$root.<top>.` a rooted one starts with is dropped, since the run keys what
// the top declares by its bare name and what an instance declares by its path
// below the top. Split out of eval_expr.cpp, which EvalMemberAccess still
// reads the name through, when that file reached the 950-line limit.

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
  // §23.6: an element of an array of instances, `arr[1]`, is named by the
  // instance name and its index, as the elaborator names the element.
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

// §23.3.1 (printed page 740): "$root is the root of the instantiation tree",
// and it serves "to disambiguate a local path (which takes precedence) from
// the rooted path", so a name headed by it is read from there and never from
// the instance that runs it: in instance A, `B.v` is A's own B while
// `$root.A_top.B.v` is the B beside A. The name is kept whole, top included,
// for FindVariable and FindNet to answer from the top of the design alone
// (SimContext::RootedStorageKey), a later top's declarations being keyed under
// its name. Empty for a name $root does not head.
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
  // A name $root heads keeps the head, for the array and its elements to be
  // read from the top of the design (SimContext::FindArrayInfo).
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
