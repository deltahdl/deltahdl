#include <algorithm>
#include <initializer_list>

#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

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
  if (rhs == nullptr) return false;
  if (Within(rhs, target)) return true;
  if (std::ranges::any_of(
          std::initializer_list<const VpiObject*>{
              rhs->index_expr, rhs->base_expr, rhs->width_expr, rhs->left_range,
              rhs->right_range},
          [&target](const VpiObject* part) {
            return VpiExpressionReads(part, target);
          })) {
    return true;
  }
  const bool kComposite =
      (rhs->type == vpiOperation || rhs->type == vpiVarSelect ||
       VpiIsVariableSelectType(rhs->type) || VpiIsTfCallType(rhs->type));
  return kComposite &&
         std::ranges::any_of(VpiSubexpressions(*rhs),
                             [&target](const VpiObject* sub) {
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

void VpiCollectVariableDriversOrLoads(VpiObject* node, bool want_driver,
                                      bool descend, VpiObject* iter) {
  const bool kDescend = descend && node->type != vpiVarSelect;
  for (auto* child : node->children) {
    if (VpiIsVariableDriverOrLoad(*child, *node, want_driver)) {
      iter->children.push_back(child);
    } else if (kDescend && VpiIsVariableSelectOrMemberType(child->type)) {
      VpiCollectVariableDriversOrLoads(child, want_driver, descend, iter);
    }
  }
}

void VpiHangOnVariablesNamed(VpiHandle holder, VpiHandle expr) {
  if (expr != nullptr && expr->type == vpiOperation) {
    for (VpiObject* operand : expr->children) {
      VpiHangOnVariablesNamed(holder, operand);
    }
    return;
  }
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
