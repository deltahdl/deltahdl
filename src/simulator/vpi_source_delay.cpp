#include "simulator/vpi_source_delay.h"

#include <algorithm>
#include <array>
#include <functional>
#include <initializer_list>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

VpiObject* VpiSourceDelayExpression(const std::vector<const Expr*>& delays,
                                    std::string_view scope_prefix,
                                    SimContext& ctx,
                                    const std::function<VpiObject*()>& alloc) {
  InstancePrefixOverride scope(ctx.InstancePrefixOverride(), scope_prefix);
  std::vector<VpiObject*> constants;
  for (const Expr* delay : delays) {
    if (delay == nullptr) break;
    // Each written delay stands as a constant expression carrying the value
    // evaluating it produced. The storage goes on the run's arena rather than
    // through SimContext::CreateVariable, which would enter the delay under a
    // name the design never declared.
    VpiObject* constant = alloc();
    constant->type = vpiConstant;
    constant->const_type = vpiIntConst;
    auto* storage = ctx.GetArena().Create<Variable>();
    storage->value = EvalExpr(delay, ctx, ctx.GetArena());
    constant->var = storage;
    constant->size = static_cast<int>(storage->value.width);
    constants.push_back(constant);
  }
  if (constants.empty()) return nullptr;
  if (constants.size() == 1) return constants.front();
  // The operands of an operation are its expression children (§36.10.3), so
  // the delays hang there in the order the source wrote them.
  VpiObject* op = alloc();
  op->type = vpiOperation;
  op->op_type = vpiListOp;
  op->children = std::move(constants);
  return op;
}

std::vector<VpiDelayInfo> VpiWrittenDelays(
    const std::array<const Expr*, 3>& delays, bool turn_off,
    std::string_view scope_prefix, SimContext& ctx) {
  std::vector<VpiDelayInfo> written;
  if (delays[0] == nullptr) return written;
  InstancePrefixOverride scope(ctx.InstancePrefixOverride(), scope_prefix);
  Arena& arena = ctx.GetArena();
  const auto kTicks = [&ctx, &arena](const Expr* delay) {
    return static_cast<double>(
        DelayValueToTicks(EvalExpr(delay, ctx, arena), ctx));
  };
  const double kRise = kTicks(delays[0]);
  const double kFall = delays[1] != nullptr ? kTicks(delays[1]) : kRise;
  const double kOff =
      delays[2] != nullptr ? kTicks(delays[2]) : std::min(kRise, kFall);
  for (const double kDelay : {kRise, kFall, kOff}) {
    VpiDelayInfo info;
    info.delay = kDelay;
    written.push_back(info);
  }
  if (!turn_off) written.pop_back();
  return written;
}

void VpiFillContAssignDelays(VpiObject* obj, const RtlirContAssign& ca,
                             std::string_view scope_prefix, SimContext& ctx,
                             const std::function<VpiObject*()>& alloc) {
  if (ca.delay == nullptr) return;
  obj->delays = VpiWrittenDelays({ca.delay, ca.delay_fall, ca.delay_decay},
                                 true, scope_prefix, ctx);
  obj->delay_expr = VpiSourceDelayExpression(
      {ca.delay, ca.delay_fall, ca.delay_decay}, scope_prefix, ctx, alloc);
}

}  // namespace delta
