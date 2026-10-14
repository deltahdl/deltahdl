// §12.7.3 "foreach-loop" in a subroutine body: the function executor's foreach,
// split out of eval_function_body.cpp, which dispatches to ExecFuncForeach.

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_body_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/foreach_dims.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

// The index values a foreach in a subroutine body steps through: the keys of
// an associative array, §12.7.3 giving the loop variable the index type and
// the traversal the array's own order, or `size` indices from `lo` up for any
// other array.
static std::vector<Logic4Vec> ForeachIndexValues(const Stmt* stmt,
                                                 const FuncExecCtx& exec) {
  if (auto* aa = FindAssocArrayOfBase(stmt->expr, exec.ctx, exec.arena)) {
    return AssocIndexValues(aa, exec.arena);
  }
  // §12.7.3 with §7.10: a queue's one dimension holds as many elements as the
  // queue does, whether the queue is a declared one or a property of an
  // object (§8.5) named bare in the method or through a handle; a declared
  // dynamic array is stored the same way and answers the same.
  uint32_t size = 0;
  int64_t lo = 0;
  ClassArrayRef ref;
  if (const QueueObject* q =
          FindQueueOfBase(stmt->expr, exec.ctx, exec.arena)) {
    size = static_cast<uint32_t>(q->elements.size());
  } else if (const StructFieldInfo* member =
                 ResolveStructArrayMember(stmt->expr, exec.ctx)) {
    // §12.7.3 with §7.2 and §7.4.2: an unpacked array member of a structure,
    // a property's `r.v` bare in the method among them, from the lower of its
    // bounds.
    size = member->elem_count;
    lo = std::min(member->elem_left, member->elem_right);
  } else if (ResolveClassArray(stmt->expr, exec.ctx, exec.arena, ref)) {
    // §12.7.3 with §7.4.2 and §7.5: a fixed-size or dynamic array property
    // (§8.5) holds its elements on the object, the declared dimension's count
    // from its lowest index for a fixed one and the object's count from 0 for
    // a dynamic one, which is what the loop variable steps through. Before
    // this the property was looked up as a variable of its name, which it is
    // not, and the loop ran no times.
    size = ref.size;
    lo = ref.lo;
  } else {
    std::string name = GetForeachArrayName(stmt->expr);
    size = name.empty() ? 0 : ForeachArraySize(name, exec.ctx);
  }
  std::vector<Logic4Vec> values;
  values.reserve(size);
  for (uint32_t i = 0; i < size; ++i) {
    Logic4Vec index =
        MakeLogic4VecVal(exec.arena, 32, static_cast<uint64_t>(lo + i));
    index.is_signed = true;
    values.push_back(index);
  }
  return values;
}

// The body of the foreach `stmt` run once per index of `element`, the second
// loop variable `var` taking each (§12.7.3): answers what the body gave last.
static FuncFlow ExecFuncForeachElement(const Stmt* stmt, Variable* var,
                                       const QueueObject* element,
                                       const FuncExecCtx& exec) {
  FuncFlow flow = FuncFlow::kNext;
  for (uint32_t p = 0; p < element->elements.size(); ++p) {
    var->value = ForeachElementIndex(*element, p, exec.arena);
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  }
  return flow;
}

// Runs the iteration loop of a foreach over the index values `keys`, pushing
// a scope that holds the (optional) loop index variable, and the second one
// where the array's elements are queues or fixed-size arrays (§12.7.3,
// ForeachElementDimOf). §12.8: a `continue` goes on to the next element, a
// `break` leaves the loop and a `return` leaves the subroutine.
static FuncFlow ExecFuncForeachLoop(const Stmt* stmt,
                                    const std::vector<Logic4Vec>& keys,
                                    const AssocArrayObject* aa,
                                    const FuncExecCtx& exec) {
  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  exec.ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = exec.ctx.CreateLocalVariable(iter_name, 32);
    iter_var->is_string = aa != nullptr && aa->is_string_key;
    // §12.7.3: an int over a fixed-size, dynamic or queue array, signed.
    iter_var->is_signed =
        aa == nullptr || (!aa->is_string_key && aa->is_index_signed);
    // §12.7.3: the loop variable has the index type of an associative array.
    TypeForeachIterVar(iter_name, aa, exec.ctx);
  }
  ForeachElementDim inner = ForeachElementDimOf(stmt, aa, exec.ctx, exec.arena);

  FuncFlow flow = FuncFlow::kNext;
  for (uint32_t i = 0; i < keys.size(); ++i) {
    if (iter_var) iter_var->value = keys[i];
    flow = inner.var == nullptr
               ? ExecFuncStmt(stmt->body, exec)
               : ExecFuncForeachElement(
                     stmt, inner.var,
                     ForeachElementQueue(inner, keys, i, exec.arena), exec);
    if (!LoopGoesOn(flow)) break;
  }

  exec.ctx.PopScope();
  return LoopExitFlow(flow);
}

// §12.7.3: the dimensions a foreach in a subroutine body walks one named loop
// variable per dimension, as nested loops: a declared array's or vector's
// (DeclaredForeachDims), a property's (ClassArrayForeachDims) or a structure
// member's (StructMemberForeachDims). None where the loop steps through
// ForeachIndexValues, whose arrays are tried first in the same order.
static std::vector<ForeachDim> FuncForeachDims(const Stmt* stmt,
                                               const FuncExecCtx& exec) {
  if (FindAssocArrayOfBase(stmt->expr, exec.ctx, exec.arena) ||
      FindQueueOfBase(stmt->expr, exec.ctx, exec.arena)) {
    return {};
  }
  if (const StructFieldInfo* member =
          ResolveStructArrayMember(stmt->expr, exec.ctx))
    return StructMemberForeachDims(stmt, *member);
  ClassArrayRef ref;
  if (ResolveClassArray(stmt->expr, exec.ctx, exec.arena, ref))
    return ClassArrayForeachDims(stmt, ref);
  return DeclaredForeachDims(stmt, exec.ctx);
}

// Runs a foreach over `dims` as nested loops, the last dimension varying
// fastest and each walked from its declared left bound (SetForeachDimVars).
static FuncFlow ExecFuncForeachDims(const Stmt* stmt,
                                    const std::vector<ForeachDim>& dims,
                                    const FuncExecCtx& exec) {
  exec.ctx.PushScope();
  std::vector<Variable*> vars = CreateForeachDimVars(dims, exec.ctx);
  uint64_t total = ForeachCombinationCount(dims);
  FuncFlow flow = FuncFlow::kNext;
  for (uint64_t n = 0; n < total; ++n) {
    SetForeachDimVars(dims, vars, n, exec.arena);
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  }
  exec.ctx.PopScope();
  return LoopExitFlow(flow);
}

// §12.7.3 makes a foreach an implicit block its label names, so §9.6.2's
// disable of that label ends the loop and goes on after it (FuncNamedScope),
// as it does for the other loops.
FuncFlow ExecFuncForeach(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  FuncNamedScope named(stmt->label, exec);
  std::vector<ForeachDim> dims = FuncForeachDims(stmt, exec);
  if (!dims.empty()) {
    FuncFlow flow = ExecFuncForeachDims(stmt, dims, exec);
    if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
    return named.Leave(flow);
  }
  auto* aa = FindAssocArrayOfBase(stmt->expr, exec.ctx, exec.arena);
  std::vector<Logic4Vec> keys = ForeachIndexValues(stmt, exec);
  FuncFlow flow = FuncFlow::kNext;
  if (!keys.empty()) {
    flow = ExecFuncForeachLoop(stmt, keys, aa, exec);
  }
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return named.Leave(flow);
}

}  // namespace delta
