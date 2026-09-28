#include "simulator/nettype_resolution.h"

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// The dynamic array the drivers are handed through. `$` begins no identifier
// a source description can write, so the name is the resolution's alone.
constexpr std::string_view kDriversName = "$nettype.drivers";

Expr* DriversCall(std::string_view func_name, Arena& arena) {
  auto* arg = arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = kDriversName;
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = func_name;
  call->args.push_back(arg);
  return call;
}

}  // namespace

void AttachNettypeResolution(Net& net, std::string_view func_name,
                             SimContext& ctx) {
  if (func_name.empty()) return;
  Expr* call = DriversCall(func_name, ctx.GetArena());
  uint32_t width = net.resolved != nullptr ? net.resolved->value.width : 0;
  net.resolve_hook = [&ctx, call, width](const std::vector<Logic4Vec>& drivers,
                                         Arena& arena) {
    // §6.6.7: the function's one input is a dynamic array holding a value
    // per driver of the net; its return value is the net's.
    QueueObject* q = ctx.CreateQueue(kDriversName, width);
    q->elements = drivers;
    ArrayInfo info;
    info.is_dynamic = true;
    info.elem_width = width;
    ctx.RegisterArray(kDriversName, info);
    return EvalExpr(call, ctx, arena);
  };
}

bool ResolveThroughNettypeFunction(Net& net, Arena& arena) {
  if (!net.is_user_nettype || !net.resolve_hook) return false;
  std::vector<Logic4Vec> all = net.drivers;
  all.insert(all.end(), net.switch_drivers.begin(), net.switch_drivers.end());
  if (all.empty()) return false;
  net.resolved->value = net.resolve_hook(all, arena);
  net.resolved->NotifyWatchers();
  return true;
}

}  // namespace delta
