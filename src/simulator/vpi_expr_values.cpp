#include "simulator/vpi_expr_values.h"

#include <algorithm>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/deferred_caller.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_expr_scope.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

Logic4Vec VpiEvaluateExpressionObject(const VpiObject& obj, SimContext& sim) {
  const VpiExprScope& scope = *obj.expr_scope;
  Process stand_in;
  stand_in.stand_in = true;
  stand_in.inst_prefix = scope.inst_prefix;
  stand_in.gen_prefixes = scope.gen_prefixes;
  const CallerStandIn kStandIn(&stand_in, sim);
  return EvalExpr(scope.expr, sim, sim.GetArena());
}

namespace {

// The aval and bval words of the value of `obj` now: the whole assignment's,
// or a cont assign bit's one bit of it.
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
  if (kBit / 64 < kValue.nwords) {
    bits.push_back((kValue.words[kBit / 64].aval >> (kBit % 64)) & 1);
    bits.push_back((kValue.words[kBit / 64].bval >> (kBit % 64)) & 1);
  }
  return bits;
}

// The storage of each net and variable the expression object `expr` reads,
// itself where it holds storage, and otherwise among its operands, at any
// depth.
void CollectReadStorage(const VpiObject* expr, std::vector<Variable*>& out) {
  if (expr == nullptr) return;
  if (expr->var != nullptr) {
    out.push_back(expr->var);
    return;
  }
  for (const VpiObject* operand : expr->children) {
    CollectReadStorage(operand, out);
  }
}

// Whether a cbValueChange registration placed on `obj` is still live.
bool HasValueChangeOn(const VpiContext& vpi, const VpiObject* obj) {
  return std::ranges::any_of(
      vpi.RegisteredCallbacks(), [obj](const s_cb_data& cb) {
        return cb.reason == cbValueChange && cb.obj != nullptr &&
               VpiObjectOf(cb.obj) == obj;
      });
}

}  // namespace

void VpiWatchContAssignChanges(VpiContext& vpi, VpiObject* obj,
                               SimContext* sim) {
  if (obj == nullptr || sim == nullptr || !VpiIsContAssignKind(obj->type) ||
      obj->expr_scope == nullptr || obj->value_change_watched) {
    return;
  }
  obj->value_change_watched = true;
  const VpiObject* assign = obj->type == vpiContAssign ? obj : obj->parent;
  std::vector<Variable*> read;
  CollectReadStorage(assign->rhs, read);
  auto held = std::make_shared<std::vector<uint64_t>>(ValueBitsNow(*obj, *sim));
  for (Variable* storage : read) {
    storage->AddWatcher([&vpi, obj, sim, held]() {
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
}

}  // namespace delta
