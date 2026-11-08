#include "simulator/vpi_expr_values.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/awaiters.h"
#include "simulator/class_object.h"
#include "simulator/deferred_caller.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_expr_scope.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

void StandInWhere(Process& stand_in, const VpiExprScope& scope) {
  stand_in.stand_in = true;
  stand_in.inst_prefix = scope.inst_prefix;
  stand_in.gen_prefixes = scope.gen_prefixes;
}

}  // namespace

Logic4Vec VpiEvaluateWhereWritten(const VpiExprScope& scope, SimContext& sim) {
  Process stand_in;
  StandInWhere(stand_in, scope);
  const CallerStandIn kStandIn(&stand_in, sim);
  if (scope.context_width == 0)
    return EvalExpr(scope.expr, sim, sim.GetArena());
  return ResizeToWidth(
      EvalExpr(scope.expr, sim, sim.GetArena(), scope.context_width),
      scope.context_width, sim.GetArena());
}

Logic4Vec VpiEvaluateExpressionObject(const VpiObject& obj, SimContext& sim) {
  return VpiEvaluateWhereWritten(*obj.expr_scope, sim);
}

namespace {

std::vector<uint64_t> ValueBitsNow(const VpiObject& obj, SimContext& sim) {
  const Logic4Vec kValue = VpiEvaluateExpressionObject(obj, sim);
  std::vector<uint64_t> bits;
  if (obj.bit_offset < 0) {
    for (uint32_t i = 0; i < kValue.nwords; ++i) {
      bits.push_back(kValue.words[i].aval);
      bits.push_back(kValue.words[i].bval);
    }
    return bits;
  }
  const auto kBit = static_cast<uint32_t>(obj.bit_offset);
  bits.push_back((kValue.words[kBit / 64].aval >> (kBit % 64)) & 1);
  bits.push_back((kValue.words[kBit / 64].bval >> (kBit % 64)) & 1);
  return bits;
}

const ClassTypeInfo* StaticPropertyClass(SimContext& sim,
                                         std::string_view name) {
  const auto kScope = name.rfind("::");
  return sim.FindClassType(name.substr(0, kScope))
      ->StaticPropertyDeclarer(name.substr(kScope + 2));
}

void WatchReads(const VpiObject& obj, SimContext& sim,
                const std::function<bool()>& notify) {
  Process stand_in;
  StandInWhere(stand_in, *obj.expr_scope);
  const CallerStandIn kStandIn(&stand_in, sim);
  std::unordered_set<std::string> names;
  CollectExprAndStaticReads(obj.expr_scope->expr, sim, names);
  std::vector<Variable*> storage;
  std::vector<const ClassTypeInfo*> classes;
  for (const std::string& name : names) {
    storage.push_back(sim.FindVariable(name));
    classes.push_back(NamesStaticProperty(sim, name)
                          ? StaticPropertyClass(sim, name)
                          : nullptr);
  }
  std::erase(storage, nullptr);
  std::erase(classes, nullptr);
  for (Variable* var : storage) var->AddWatcher(notify);
  for (const ClassTypeInfo* cls : classes) cls->AddStaticWatcher(notify);
}

bool HasValueChangeOn(const VpiContext& vpi, const VpiObject* obj) {
  return std::ranges::any_of(
      vpi.RegisteredCallbacks(), [obj](const s_cb_data& cb) {
        return cb.reason == cbValueChange && VpiObjectOf(cb.obj) == obj;
      });
}

}  // namespace

void VpiWatchContAssignChanges(VpiContext& vpi, VpiObject* obj,
                               SimContext* sim) {
  if (sim == nullptr || !VpiIsContAssignKind(obj->type) ||
      obj->value_change_watched) {
    return;
  }
  obj->value_change_watched = true;
  auto held = std::make_shared<std::vector<uint64_t>>(ValueBitsNow(*obj, *sim));
  WatchReads(*obj, *sim, [&vpi, obj, sim, held]() {
    if (!HasValueChangeOn(vpi, obj)) {
      obj->value_change_watched = false;
      return true;
    }
    std::vector<uint64_t> now = ValueBitsNow(*obj, *sim);
    if (now == *held) return false;
    *held = std::move(now);
    vpi.DispatchCallbacks(cbValueChange, obj);
    return false;
  });
}

}  // namespace delta
