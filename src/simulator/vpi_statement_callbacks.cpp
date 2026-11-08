#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_stmt.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_stmt_objects.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

bool HeldBy(const VpiObject& obj, const VpiObject& scope) {
  for (const VpiObject* at = obj.parent; at != nullptr; at = at->parent) {
    if (at == &scope) return true;
  }
  return false;
}

}  // namespace

void VpiContext::NoteStmtExecuting(const Stmt* stmt, std::string prefix) {
  VpiHandle frame = sim_ctx_ != nullptr ? ActiveFrame() : nullptr;
  if (frame == nullptr && !stmt_callbacks_registered_) return;
  VpiObject* obj = VpiStmtObjectFor(stmt_objects_, stmt, std::move(prefix));
  if (frame != nullptr) frame->frame_facts.stmt = obj;
  if (stmt_callbacks_registered_ && obj != nullptr) {
    DispatchCallbacks(cbStmt, obj);
    if (obj->type == vpiEventStmt) DispatchCallbacks(cbValueChange, obj);
  }
}

void VpiContext::NoteForce(int reason, const Variable* var, const Stmt* stmt,
                           std::string prefix) {
  if (!HasCallbackFor(callbacks_, reason)) return;
  VpiObject* stmt_obj =
      VpiStmtObjectFor(stmt_objects_, stmt, std::move(prefix));
  const size_t kCount = callbacks_.size();
  for (size_t i = 0; i < kCount; ++i) {
    if (callbacks_[i].reason != reason || callbacks_[i].cb_rtn == nullptr) {
      continue;
    }
    VpiObject* placed = VpiObjectOf(callbacks_[i].obj);
    if (placed != nullptr && placed->var != var) continue;
    s_cb_data data = callbacks_[i];
    s_vpi_value value{};
    VpiObject* target = placed;
    if (target == nullptr && stmt_obj != nullptr) target = stmt_obj->lhs;
    if (target != nullptr && data.value != nullptr &&
        data.value->format != vpiSuppressVal) {
      value.format = data.value->format;
      GetValue(target, &value);
      data.value = &value;
    }
    data.obj = VpiHandleOf(stmt_obj);
    Deliver(data);
  }
}

void VpiContext::NoteDisabled(const Stmt* disable, std::string prefix) {
  if (!HasCallbackFor(callbacks_, cbDisable)) return;
  VpiObject* target = VpiDisableExpr(
      VpiStmtObjectFor(stmt_objects_, disable, std::move(prefix)));
  if (target == nullptr) return;
  std::vector<VpiObject*> held;
  for (const auto& [site, call] : call_site_objects_) {
    if ((call->type == vpiSysTaskCall || call->type == vpiSysFuncCall) &&
        HeldBy(*call, *target)) {
      held.push_back(call);
    }
  }
  if (held.empty()) return;
  DispatchCallbacks(cbDisable, target);
  for (VpiObject* call : held) DispatchCallbacks(cbDisable, call);
}

}  // namespace delta
