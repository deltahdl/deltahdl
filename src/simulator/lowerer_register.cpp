#include "simulator/lowerer_register.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"

namespace delta {

void RecordPackedRange(const DataType* dt, Variable* v, SimContext& ctx,
                       Arena& arena) {
  if (!dt || !dt->packed_dim_left || !dt->packed_dim_right) return;
  auto eval = [&](const Expr* e) {
    return static_cast<int64_t>(EvalExpr(e, ctx, arena).ToUint64());
  };
  auto span = [](int64_t l, int64_t r) {
    return static_cast<uint64_t>((l >= r ? l - r : r - l) + 1);
  };
  uint64_t stride = 1;
  for (const auto& [l, r] : dt->extra_packed_dims)
    stride *= span(eval(l), eval(r));
  if (stride > 1) v->packed_elem_width = static_cast<uint32_t>(stride);
  PackedRange range{eval(dt->packed_dim_left), eval(dt->packed_dim_right)};
  // The elaborator sized this storage from the same dimensions. Bounds that do
  // not account for its width came from an expression this scope cannot fold,
  // and a range read off them would misaddress every bit, so leave the storage
  // addressed as [width-1:0].
  if (span(range.left, range.right) * stride != v->value.width) return;
  v->packed_range = range;
  v->has_packed_range = true;
}

void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx, Arena& arena) {
  for (const auto& net : mod->nets) {
    auto* created = ctx.CreateNet(
        net.name, net.net_type, net.width,
        NetSpec{net.charge_strength, net.decay_ticks, net.is_user_nettype,
                net.resolve_func, net.is_signed});
    RecordPackedRange(net.dtype, created->resolved, ctx, arena);
  }
}

// §23.3.3.2: an input port "shall have the default initial value corresponding
// to the data type" when left unconnected, and Table 6-7 gives that value per
// type. Fresh storage is created holding x, which is already the 4-state
// integral default, so only a type whose default is zero needs writing. String
// and event are excluded for the same reason the body declaration excludes
// them: their defaults are an empty string and a new event, neither of which
// is a bit pattern this write would produce.
bool PortDefaultsToZero(const RtlirPort& port) {
  if (port.type_kind == DataTypeKind::kString ||
      port.type_kind == DataTypeKind::kEvent) {
    return false;
  }
  return !Is4stateType(port.type_kind);
}

void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx,
                         Arena& arena) {
  for (const auto& port : mod->ports) {
    if (!ctx.FindVariable(port.name)) {
      auto* v = ctx.CreateVariable(port.name, port.width);
      if (PortDefaultsToZero(port))
        v->value = MakeLogic4VecVal(arena, port.width, 0);
      if (port.is_signed) v->is_signed = true;
      // §21.7.5 (Table 21-11): a port declared with a SystemVerilog data type
      // is dumped under that type's 1364-2005 masquerade, just as a module-body
      // declaration of the same type is. A port reaching here has no body
      // declaration that already recorded its kind, so record the declared
      // keyword now. The port carries only that keyword, so an enum port keeps
      // the default enum mapping rather than any specified base type.
      ctx.SetVcdVarKind(port.name, port.type_kind);
    }
  }
}

void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx) {
  for (auto* func : mod->function_decls) {
    ctx.RegisterFunction(func->name, func);
  }
  for (auto* let_decl : mod->let_decls) {
    ctx.RegisterLetDecl(let_decl->name, let_decl);
  }
}

void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx) {
  for (auto* seq_decl : mod->sequence_decls) {
    ctx.RegisterSequenceDecl(seq_decl->name, seq_decl);

    std::string ep_name = std::string("__seq_") + std::string(seq_decl->name);
    if (!ctx.FindVariable(ep_name)) {
      // variables_ keys by string_view, so the key's backing string must
      // outlive the map; intern it in the arena. A local std::string would
      // dangle and make every later FindVariable("__seq_<name>") miss.
      auto* stored = ctx.GetArena().Create<std::string>(std::move(ep_name));
      auto* ep_var = ctx.CreateVariable(*stored, 1);
      ep_var->is_event = true;
    }
  }
}

void RegisterProcessClassType(SimContext& ctx, Arena& arena) {
  auto* proc_type = arena.Create<ClassTypeInfo>();
  proc_type->name = "process";
  proc_type->enum_members["FINISHED"] = 0;
  proc_type->enum_members["RUNNING"] = 1;
  proc_type->enum_members["WAITING"] = 2;
  proc_type->enum_members["SUSPENDED"] = 3;
  proc_type->enum_members["KILLED"] = 4;
  ctx.RegisterClassType("process", proc_type);
}

}  // namespace delta
