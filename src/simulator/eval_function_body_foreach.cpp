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

static std::vector<Logic4Vec> ForeachIndexValues(const Stmt* stmt,
                                                 const FuncExecCtx& exec) {
  if (auto* aa = FindAssocArrayOfBase(stmt->expr, exec.ctx, exec.arena)) {
    return AssocIndexValues(aa, exec.arena);
  }
  uint32_t size = 0;
  int64_t lo = 0;
  ClassArrayRef ref;
  if (const QueueObject* q =
          FindQueueOfBase(stmt->expr, exec.ctx, exec.arena)) {
    size = static_cast<uint32_t>(q->elements.size());
  } else if (const StructFieldInfo* member =
                 ResolveStructArrayMember(stmt->expr, exec.ctx)) {
    size = member->elem_count;
    lo = std::min(member->elem_left, member->elem_right);
  } else if (ResolveClassArray(stmt->expr, exec.ctx, exec.arena, ref)) {
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
    iter_var->is_signed =
        aa == nullptr || (!aa->is_string_key && aa->is_index_signed);
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
