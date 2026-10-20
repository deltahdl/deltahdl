#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_expr.h"
#include "simulator/expr_walk.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// §16.9.3: whether `e` calls one of the sampled value functions that look
// back through the history of their argument.
bool IsPastDirectedCall(const Expr* e) {
  if (e->kind != ExprKind::kSystemCall) return false;
  return e->callee == "$past" || e->callee == "$rose" || e->callee == "$fell" ||
         e->callee == "$stable" || e->callee == "$changed";
}

}  // namespace

void CollectPastDirectedSites(const Expr* e, std::vector<const Expr*>& sites) {
  ForEachSubExpr(e, [&sites](const Expr* sub) {
    if (IsPastDirectedCall(sub)) sites.push_back(sub);
  });
}

std::string HierarchicalEndPoint(std::string_view path, SimContext& ctx) {
  size_t dot = path.rfind('.');
  if (dot == std::string_view::npos) return {};
  std::string ep_name = std::string(path.substr(0, dot)) + ".__seq_" +
                        std::string(path.substr(dot + 1));
  const Variable* ep = ctx.FindVariable(ep_name);
  if (ep == nullptr || !ep->is_event) return {};
  return ep_name;
}

}  // namespace delta
