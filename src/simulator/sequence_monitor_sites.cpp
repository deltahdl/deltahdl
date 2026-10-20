#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_expr.h"
#include "simulator/expr_walk.h"
#include "simulator/sequence_flatten.h"
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

// §16.9.3: a sampled value function in a sequence is clocked by the
// sequence's clock, and the history it looks back through is sampled at
// every tick of that clock whether or not an attempt reads the operand at
// the tick -- `$rose(ready)` standing after `inst` in a chain still answers
// the tick before. The calls are collected once, over every chain of the
// body, and each is evaluated as the monitor resumes so that its sample for
// the tick is recorded; an attempt reading it records the same value over
// it.
void CollectPastDirectedSites(const LinearSequence& body,
                              std::vector<const Expr*>& sites) {
  ForEachLinearSequenceExpr(
      body, [&sites](const Expr* e) { CollectPastDirectedSites(e, sites); });
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
