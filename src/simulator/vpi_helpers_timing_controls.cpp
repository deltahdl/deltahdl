#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

VpiHandle VpiEventControlStmt(VpiHandle event_control) {
  if (!event_control) return nullptr;
  if (event_control->parent && event_control->parent->type == vpiAssignment) {
    return nullptr;
  }
  for (auto* child : event_control->children) {
    if (VpiIsScopeBodyStmtObject(child)) return child;
  }
  return nullptr;
}

VpiHandle VpiEventControlConditionExpr(VpiHandle event_control) {
  if (!event_control) return nullptr;
  for (auto* child : event_control->children) {
    if (VpiIsOperandObject(child) || child->type == vpiSequenceInst ||
        child->type == vpiNamedEvent || child->type == vpiClockingBlock) {
      return child;
    }
  }
  return nullptr;
}

VpiHandle VpiRepeatControlExpr(VpiHandle repeat_control) {
  if (!repeat_control) return nullptr;
  for (auto* child : repeat_control->children) {
    if (VpiIsOperandObject(child)) return child;
  }
  return nullptr;
}

VpiHandle VpiDelayControlStmt(VpiHandle delay_control) {
  if (!delay_control) return nullptr;
  if (delay_control->parent && delay_control->parent->type == vpiAssignment) {
    return nullptr;
  }
  for (auto* child : delay_control->children) {
    if (VpiIsScopeBodyStmtObject(child)) return child;
  }
  return nullptr;
}

VpiHandle VpiDelayControlDelayExpr(VpiHandle delay_control) {
  if (!delay_control) return nullptr;
  for (auto* child : delay_control->children) {
    if (VpiIsOperandObject(child)) return child;
  }
  return nullptr;
}

}  // namespace delta
