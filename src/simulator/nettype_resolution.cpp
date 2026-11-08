#include "simulator/nettype_resolution.h"

#include <cstddef>
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

constexpr std::string_view kDriversName = "$nettype.drivers";

Expr* Identifier(std::string_view text, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = text;
  return id;
}

Expr* ScopedName(std::string_view qualified, Arena& arena) {
  size_t sep = qualified.find("::");
  Expr* name = Identifier(qualified.substr(0, sep), arena);
  while (sep != std::string_view::npos) {
    const size_t kStart = sep + 2;
    sep = qualified.find("::", kStart);
    auto* access = arena.Create<Expr>();
    access->kind = ExprKind::kMemberAccess;
    access->lhs = name;
    access->rhs = Identifier(qualified.substr(kStart, sep - kStart), arena);
    access->is_scope_resolution = true;
    name = access;
  }
  return name;
}

Expr* DriversCall(std::string_view func_name, Arena& arena) {
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  if (func_name.find("::") == std::string_view::npos) {
    call->callee = func_name;
  } else {
    call->lhs = ScopedName(func_name, arena);
  }
  call->args.push_back(Identifier(kDriversName, arena));
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
