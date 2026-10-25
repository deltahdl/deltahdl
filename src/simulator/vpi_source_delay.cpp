#include "simulator/vpi_source_delay.h"

#include <algorithm>
#include <array>
#include <cstdint>
#include <functional>
#include <initializer_list>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
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

namespace {

// The value `delay` evaluates to, in ticks, with the run's min:typ:max
// selection set to `mode` (§11.11).
double TicksUnder(const Expr* delay, DelayMode mode, SimContext& ctx) {
  const DelayMode kSaved = ctx.GetDelayMode();
  ctx.SetDelayMode(mode);
  const uint64_t kTicks = DelayExprToTicks(delay, ctx, ctx.GetArena());
  ctx.SetDelayMode(kSaved);
  return static_cast<double>(kTicks);
}

// The smaller of each of `a`'s and `b`'s values, a turn-off delay none was
// written for (§10.3.3, §28.16).
VpiDelayInfo SmallerOf(const VpiDelayInfo& a, const VpiDelayInfo& b) {
  VpiDelayInfo smaller;
  smaller.delay = std::min(a.delay, b.delay);
  smaller.min_delay = std::min(a.min_delay, b.min_delay);
  smaller.typ_delay = std::min(a.typ_delay, b.typ_delay);
  smaller.max_delay = std::min(a.max_delay, b.max_delay);
  return smaller;
}

}  // namespace

VpiDelayInfo VpiWrittenDelay(const Expr* delay, SimContext& ctx) {
  VpiDelayInfo info;
  info.delay = TicksUnder(delay, ctx.GetDelayMode(), ctx);
  info.min_delay = TicksUnder(delay, DelayMode::kMin, ctx);
  info.typ_delay = TicksUnder(delay, DelayMode::kTyp, ctx);
  info.max_delay = TicksUnder(delay, DelayMode::kMax, ctx);
  return info;
}

std::vector<VpiDelayInfo> VpiWrittenDelays(
    const std::array<const Expr*, 3>& delays, bool turn_off,
    std::string_view scope_prefix, SimContext& ctx) {
  std::vector<VpiDelayInfo> written;
  if (delays[0] == nullptr) return written;
  InstancePrefixOverride scope(ctx.InstancePrefixOverride(), scope_prefix);
  const VpiDelayInfo kRise = VpiWrittenDelay(delays[0], ctx);
  const VpiDelayInfo kFall =
      delays[1] != nullptr ? VpiWrittenDelay(delays[1], ctx) : kRise;
  written = {kRise, kFall};
  if (turn_off) {
    written.push_back(delays[2] != nullptr ? VpiWrittenDelay(delays[2], ctx)
                                           : SmallerOf(kRise, kFall));
  }
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
