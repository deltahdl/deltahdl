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

// Whether `obj` is the variable `var` or stands inside it: a select, a bit, an
// element or a member of it at any depth.
bool WithinVariable(const VpiObject* obj, const VpiObject& var) {
  for (; obj != nullptr; obj = obj->parent) {
    if (obj == &var) return true;
  }
  return false;
}

// Whether the target `lhs` of an assignment writes `var`: names it, a part of
// it, or names it among the operands of a concatenation.
bool Drives(const VpiObject* lhs, const VpiObject& var) {
  if (WithinVariable(lhs, var)) return true;
  return lhs != nullptr && lhs->type == vpiOperation &&
         std::ranges::any_of(lhs->children, [&var](const VpiObject* operand) {
           return Drives(operand, var);
         });
}

// Whether the expression `rhs` reads `var`: names it or a part of it, or reads
// it as an operand, an index of a select or an argument of a call at any
// depth.
bool Reads(const VpiObject* rhs, const VpiObject& var) {
  if (WithinVariable(rhs, var)) return true;
  const bool kComposite =
      rhs != nullptr &&
      (rhs->type == vpiOperation || rhs->type == vpiVarSelect ||
       VpiIsVariableSelectType(rhs->type) || VpiIsTfCallType(rhs->type));
  return kComposite &&
         std::ranges::any_of(rhs->children, [&var](const VpiObject* sub) {
           return Reads(sub, var);
         });
}

}  // namespace

bool VpiIsVariableDriverOrLoad(const VpiObject& child, const VpiObject& var,
                               bool want_driver) {
  if (!(want_driver ? VpiIsVariableDriverType(child.type)
                    : VpiIsVariableLoadType(child.type))) {
    return false;
  }
  if (child.type == vpiPort || child.type == vpiContAssignBit) return true;
  return want_driver ? Drives(child.lhs, var) : Reads(child.rhs, var);
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
