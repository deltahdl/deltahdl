#include <cstddef>
#include <string>
#include <string_view>
#include <utility>

#include "parser/ast_stmt.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_stmt_objects.h"
#include "simulator/vpi_user.h"

// §37.43 and §38.36.1: what the run tells the VPI context of the statements it
// executes -- each statement as it begins, a force or release, a disable --
// and the callbacks placed on them that are called for it.

namespace delta {

void VpiContext::NoteStmtExecuting(const Stmt* stmt, std::string prefix) {
  // §37.43 detail 4: the statement beginning in a frame is the one active
  // within it, and stays the one detail 5 reports once the statement has
  // activated a frame of its own, until the next one in this frame begins.
  VpiHandle frame = sim_ctx_ != nullptr ? ActiveFrame() : nullptr;
  if (frame == nullptr && !stmt_callbacks_registered_) return;
  VpiObject* obj = VpiStmtObjectFor(stmt_objects_, stmt, std::move(prefix));
  if (frame != nullptr) frame->frame_facts.stmt = obj;
  if (stmt_callbacks_registered_ && obj != nullptr) {
    DispatchCallbacks(cbStmt, obj);
    // §38.36.1: an event statement has no value, and a cbValueChange placed
    // on one is called each time it executes, with value NULL (Deliver).
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
    // §38.36.1: a callback placed on an object is called for a force,
    // release, assign or deassign of that object, one placed on none for
    // every one, its obj the statement and its value the target's after it.
    VpiObject* placed = VpiObjectOf(callbacks_[i].obj);
    if (placed != nullptr && placed->var != var) continue;
    s_cb_data data = callbacks_[i];
    s_vpi_value value{};
    // §38.36.1: the value is the statement's left-hand side's after it, read
    // from the object the callback is placed on or, placed on none, from the
    // statement's left-hand side.
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

void VpiContext::NoteDisabled(std::string_view label, std::string prefix) {
  if (!HasCallbackFor(callbacks_, cbDisable)) return;
  // §38.36.1: the named begin or fork the disable names, among the blocks of
  // the instance it ran in.
  if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  const std::string_view kLeaf = label.substr(label.rfind('.') + 1);
  for (const auto& [key, obj] : stmt_objects_) {
    if (key.second == prefix && obj->name == kLeaf &&
        (obj->type == vpiNamedBegin || obj->type == vpiNamedFork)) {
      DispatchCallbacks(cbDisable, obj);
      return;
    }
  }
}

}  // namespace delta
