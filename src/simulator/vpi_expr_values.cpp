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

// Makes `stand_in` a process of the instance and generate blocks `scope`
// records, which reads names as a process running there would.
void StandInWhere(Process& stand_in, const VpiExprScope& scope) {
  stand_in.stand_in = true;
  stand_in.inst_prefix = scope.inst_prefix;
  stand_in.gen_prefixes = scope.gen_prefixes;
}

}  // namespace

Logic4Vec VpiEvaluateExpressionObject(const VpiObject& obj, SimContext& sim) {
  const VpiExprScope& scope = *obj.expr_scope;
  Process stand_in;
  StandInWhere(stand_in, scope);
  const CallerStandIn kStandIn(&stand_in, sim);
  if (scope.context_width == 0)
    return EvalExpr(scope.expr, sim, sim.GetArena());
  return ResizeToWidth(
      EvalExpr(scope.expr, sim, sim.GetArena(), scope.context_width),
      scope.context_width, sim.GetArena());
}

namespace {

// The aval and bval words of the value of `obj` now: the whole assignment's,
// or a cont assign bit's one bit of it. A bit lies below the width of the left
// side, which the value is evaluated at, so the word holding it is there.
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

// The class whose own storage the static property `name`, written `C::n`, is
// (§8.9), which NamesStaticProperty has found it to be.
const ClassTypeInfo* StaticPropertyClass(SimContext& sim,
                                         std::string_view name) {
  const auto kScope = name.rfind("::");
  return sim.FindClassType(name.substr(0, kScope))
      ->StaticPropertyDeclarer(name.substr(kScope + 2));
}

// Has `notify` called as anything changes that the right-hand side of the
// continuous assignment or cont assign bit `obj` reads (§10.3.2): the storage
// of each net and variable, and the class of each static class property,
// which its writes notify (§8.9). The names are those the source
// expression reads, resolved where it stands, so a right side the VPI model
// gives no expression object, or one whose operands it models only in part, is
// watched all the same; a name that stands for neither, which no change can
// come to, is dropped.
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

// Whether a cbValueChange registration placed on `obj` is still live. One
// placed on no object is not placed on `obj`, which is never null.
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
