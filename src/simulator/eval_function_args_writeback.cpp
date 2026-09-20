#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// The root an actual is written on: the base of a select chain, else the
// actual itself.
static const Expr* SelectRoot(const Expr* actual) {
  while (actual && actual->kind == ExprKind::kSelect) actual = actual->base;
  return actual;
}

// Whether the formal's value is carried back into the actual when the
// subroutine returns. §13.5.2 (printed page 349) has an output or inout formal
// copied to its actual then, and lists a class property and a member of an
// unpacked structure among what may be passed by reference. Neither of those
// is a variable of its own -- a property is a field of its object and a
// member a window of the structure's variable -- so there is nothing for the
// ref binds to alias and the formal took BindValueArg's copy: `add(s.b, 20)`
// and `add(h.v, 5)` left 5 and 60 standing. The copy is carried back into the
// member or property here, through the assignment the actual takes as a
// target, exactly as a queue or associative-array element's is by
// WritebackQueueRefs and WritebackAssocRefs. A ref actual rooted anywhere
// else is either aliased, and needs no copy-out, or is no target at all; a
// const ref formal (printed page 350) is read only.
static bool CopiesOutOnReturn(const FunctionArg& formal, const Expr* actual) {
  if (formal.direction == Direction::kOutput ||
      formal.direction == Direction::kInout) {
    return true;
  }
  if (formal.direction != Direction::kRef || formal.is_const) return false;
  // A formal declared with unpacked dimensions is an aggregate, which the
  // copy BindValueArg makes of a member or property does not stand for.
  if (!formal.unpacked_dims.empty()) return false;
  const Expr* root = SelectRoot(actual);
  return root != nullptr && root->kind == ExprKind::kMemberAccess;
}

// One element of an output or inout formal declared with an unpacked
// dimension, and the caller's element variable it is copied into.
struct ElementWriteback {
  std::string target;
  Logic4Vec value;
};

// §13.3 (printed page 337) writes mytask4's `output [3:0][7:0] y[1:0]`, a
// formal with an unpacked dimension, and §13.5 (printed page 348) has the
// return pass the values of the output and inout formals to the variables of
// the call. TryBindArrayArg materializes such a formal as one variable per
// element, `yo[0]` and `yo[1]`, with the shape recorded in the callee's scope
// and no variable of the formal's own name -- which was the one name the
// copy-out looked up, so every element of the actual kept its x. The elements
// are gathered here, while the callee's scope still holds the shape and the
// element variables; the actual is the identifier TryBindArrayArg bound the
// formal from, whose elements are the `y[idx]` variables CreateArrayElements
// (lowerer_var.cpp) declares. Each value takes its own words, as the copy in
// did: the formal's variable goes with the call, and the caller's element is
// what keeps the value.
static void CollectElementWritebacks(const FunctionArg& formal,
                                     const Expr* actual, SimContext& ctx,
                                     Arena& arena,
                                     std::vector<ElementWriteback>& out) {
  if (formal.unpacked_dims.empty() || actual == nullptr ||
      actual->kind != ExprKind::kIdentifier) {
    return;
  }
  const ArrayInfo* info = ctx.FindArrayInfo(formal.name);
  if (info == nullptr) return;
  for (uint32_t j = 0; j < info->size; ++j) {
    std::string suffix = "[" + std::to_string(info->lo + j) + "]";
    auto* elem = ctx.FindLocalVariable(std::string(formal.name) + suffix);
    if (elem == nullptr) continue;
    out.push_back(
        {std::string(actual->text) + suffix, OwnRhsWords(elem->value, arena)});
  }
}

// The actual is an expression of the caller's, so it is assigned with the
// callee's scope, the top of the stack at this point, taken off the stack and
// put back after: an actual spelled like the formal would otherwise resolve
// to the formal and the caller's variable never change. An element of an
// array actual is a variable of the caller's, named rather than written as an
// expression, and is stored into as §11.4.1's compound operators store into a
// variable: sized to it, coerced where it is 2-state, declined while it is
// forced, its watchers told.
static void AssignInCallerScope(
    const std::vector<std::pair<const Expr*, Logic4Vec>>& writes,
    const std::vector<ElementWriteback>& element_writes, SimContext& ctx,
    Arena& arena) {
  std::vector<Scope> stack = ctx.SwapScopeStack({});
  Scope callee = std::move(stack.back());
  stack.pop_back();
  ctx.SwapScopeStack(std::move(stack));
  for (const auto& [target, value] : writes) {
    PerformBlockingAssign(target, value, ctx, arena);
  }
  for (const auto& [target, value] : element_writes) {
    if (auto* elem = ctx.FindVariable(target)) WriteVar(elem, value, arena);
  }
  stack = ctx.SwapScopeStack({});
  stack.push_back(std::move(callee));
  ctx.SwapScopeStack(std::move(stack));
}

// §13.5.2: an output or inout formal is copied to its actual when the
// subroutine returns, and so is a ref formal bound to a member or property
// (CopiesOutOnReturn). A formal with no variable of its own name is one
// TryBindArrayArg spread over per-element variables, copied out element by
// element (CollectElementWritebacks).
void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena) {
  std::vector<std::pair<const Expr*, Logic4Vec>> writes;
  std::vector<ElementWriteback> element_writes;
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    const FunctionArg& formal = func->func_args[i];
    int ai = ResolveArgIndex(func, expr, i);
    const Expr* actual =
        ai >= 0 ? expr->args[static_cast<size_t>(ai)] : nullptr;
    if (!CopiesOutOnReturn(formal, actual)) continue;
    auto* local = ctx.FindLocalVariable(formal.name);
    if (!local) {
      CollectElementWritebacks(formal, actual, ctx, arena, element_writes);
      continue;
    }
    const Expr* wb_target = actual ? actual : formal.default_value;
    if (!wb_target) continue;
    writes.emplace_back(wb_target, local->value);
  }
  if (writes.empty() && element_writes.empty()) return;
  AssignInCallerScope(writes, element_writes, ctx, arena);
}

}  // namespace delta
