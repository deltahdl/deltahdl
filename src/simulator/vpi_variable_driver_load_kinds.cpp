#include <algorithm>

#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

// ===========================================================================
// §37.21 Variable drivers and loads.
// ===========================================================================

namespace {

// Whether `obj` is `target` or stands inside it: a select, a bit, an element
// or a member of it at any depth.
bool Within(const VpiObject* obj, const VpiObject& target) {
  for (; obj != nullptr; obj = obj->parent) {
    if (obj == &target) return true;
  }
  return false;
}

}  // namespace

bool VpiAssignTargetWrites(const VpiObject* lhs, const VpiObject& target) {
  if (Within(lhs, target)) return true;
  return lhs != nullptr && lhs->type == vpiOperation &&
         std::ranges::any_of(lhs->children,
                             [&target](const VpiObject* operand) {
                               return VpiAssignTargetWrites(operand, target);
                             });
}

bool VpiExpressionReads(const VpiObject* rhs, const VpiObject& target) {
  if (Within(rhs, target)) return true;
  const bool kComposite =
      rhs != nullptr &&
      (rhs->type == vpiOperation || rhs->type == vpiVarSelect ||
       VpiIsVariableSelectType(rhs->type) || VpiIsTfCallType(rhs->type));
  return kComposite &&
         std::ranges::any_of(rhs->children, [&target](const VpiObject* sub) {
           return VpiExpressionReads(sub, target);
         });
}

bool VpiIsVariableDriverOrLoad(const VpiObject& child, const VpiObject& var,
                               bool want_driver) {
  if (!(want_driver ? VpiIsVariableDriverType(child.type)
                    : VpiIsVariableLoadType(child.type))) {
    return false;
  }
  if (child.type == vpiPort || child.type == vpiContAssignBit) return true;
  return want_driver ? VpiAssignTargetWrites(child.lhs, var)
                     : VpiExpressionReads(child.rhs, var);
}

void VpiHangOnVariablesNamed(VpiHandle holder, VpiHandle expr) {
  if (expr != nullptr && expr->type == vpiOperation) {
    for (VpiObject* operand : expr->children) {
      VpiHangOnVariablesNamed(holder, operand);
    }
    return;
  }
  // A select climbs to what it selects from, and an element or a member to
  // the variable holding it, up to the variable the expression names a part
  // of.
  VpiObject* var = expr;
  while (var != nullptr && var->parent != nullptr &&
         (VpiIsVariablesType(var->parent->type) || var->type == vpiVarSelect ||
          VpiIsVariableSelectType(var->type))) {
    var = var->parent;
  }
  if (var == nullptr || !VpiIsVariablesType(var->type) ||
      std::ranges::find(var->children, holder) != var->children.end()) {
    return;
  }
  var->children.push_back(holder);
}

}  // namespace delta
