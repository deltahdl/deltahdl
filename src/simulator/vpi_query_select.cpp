#include "simulator/vpi_query_select.h"

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

VpiHandle VpiSelectPrefix(VpiHandle obj) {
  VpiHandle parent = obj->parent;
  if (parent == nullptr) return nullptr;
  if (!VpiIsNetsType(parent->type) && !VpiIsVariablesType(parent->type)) {
    return nullptr;
  }
  return parent;
}

bool VpiNetOrVariableConstantSelect(VpiHandle obj) {
  bool all_indices_constant = true;
  bool all_elements_static_members = true;
  for (VpiHandle node = obj, prefix = VpiSelectPrefix(obj); prefix != nullptr;
       node = prefix, prefix = VpiSelectPrefix(prefix)) {
    if (node->index_expr != nullptr &&
        !VpiIsElaborationConstant(node->index_expr)) {
      all_indices_constant = false;
    }
    if (prefix->array_type != 0 && prefix->array_type != vpiStaticArray) {
      all_elements_static_members = false;
    }
  }
  const bool kHasParent = VpiSelectPrefix(obj) != nullptr;
  if (VpiIsNetsType(obj->type)) {
    return VpiNetConstantSelect(kHasParent, all_indices_constant,
                                all_elements_static_members);
  }
  VpiConstantSelectQuery query;
  query.has_static_lifetime = !obj->automatic;
  query.has_parent = kHasParent;
  query.all_indices_constant = all_indices_constant;
  query.all_elements_static_members = all_elements_static_members;
  return VpiConstantSelect(query);
}

bool VpiPartSelectConstantSelect(VpiHandle select) {
  const VpiHandle kParent = select->parent;
  if (kParent == nullptr || VpiGetConstantSelect(kParent) == 0) return false;
  if (kParent->array_type != 0 && kParent->array_type != vpiStaticArray) {
    return false;
  }
  if (select->type == vpiIndexedPartSelect) {
    return VpiIsElaborationConstant(select->base_expr) &&
           VpiIsElaborationConstant(select->width_expr);
  }
  return VpiIsElaborationConstant(select->left_range) &&
         VpiIsElaborationConstant(select->right_range);
}

}  // namespace

int VpiGetConstantSelect(VpiHandle obj) {
  if (VpiIsNetsType(obj->type) || VpiIsVariablesType(obj->type)) {
    return VpiNetOrVariableConstantSelect(obj) ? 1 : 0;
  }
  if (obj->type == vpiPartSelect || obj->type == vpiIndexedPartSelect) {
    return VpiPartSelectConstantSelect(obj) ? 1 : 0;
  }
  if (VpiVarSelectConstantSelectOf(obj)) return 1;
  return VpiBitSelectConstantSelectOf(obj) ? 1 : 0;
}

}  // namespace delta
