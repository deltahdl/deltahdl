#include "simulator/vpi_query_select.h"

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The prefix §37.16 detail 23 and §37.17 detail 27 call a net's or variable's
// parent: the net or variable a bit, member or element is selected out of. A
// net or variable declared in a scope has none, the scope holding it being no
// such prefix.
VpiHandle VpiSelectPrefix(VpiHandle obj) {
  VpiHandle parent = obj->parent;
  if (parent == nullptr) return nullptr;
  if (!VpiIsNetsType(parent->type) && !VpiIsVariablesType(parent->type)) {
    return nullptr;
  }
  return parent;
}

// §37.16 detail 23 for a net, §37.17 detail 27 for a variable, each bit and
// member included: one with no parent is a constant select (a variable only
// when its lifetime is static), and one with a parent is when every index
// selecting it out of the outermost net or variable is a constant and every
// element on the way is a member or an element of an array with static
// bounds. A struct or union member, a packed element and a bit always are; an
// element of a dynamic, associative or queue array is not.
bool VpiNetOrVariableConstantSelect(VpiHandle obj) {
  bool all_indices_constant = true;
  bool all_elements_static_members = true;
  for (VpiHandle node = obj, prefix = VpiSelectPrefix(obj); prefix != nullptr;
       node = prefix, prefix = VpiSelectPrefix(prefix)) {
    if (node->index_expr != nullptr && node->index_expr->type != vpiConstant) {
      all_indices_constant = false;
    }
    // §37.17 detail 21: an array var's vpiArrayType says whether its bounds
    // are static; every other prefix records none.
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

// §37.59 detail 9: a part select or an indexed part select is a constant
// select when its parent is, the parent is an array with static bounds, and
// each range expression it is written with - the two bounds, or the base and
// the width - is an elaboration-time constant.
bool VpiPartSelectConstantSelect(VpiHandle select) {
  const VpiHandle kParent = select->parent;
  if (kParent == nullptr || VpiGetConstantSelect(kParent) == 0) return false;
  if (kParent->array_type != 0 && kParent->array_type != vpiStaticArray) {
    return false;
  }
  const auto kConstant = [](const VpiObject* range) {
    return range != nullptr && range->type == vpiConstant;
  };
  if (select->type == vpiIndexedPartSelect) {
    return kConstant(select->base_expr) && kConstant(select->width_expr);
  }
  return kConstant(select->left_range) && kConstant(select->right_range);
}

}  // namespace

// §37.19: the figure draws "-> constant selection / bool: vpiConstantSelect" on
// a var select, and §37.4.2's key reads a Boolean property with vpi_get().
// Nothing answered the property at all, so the one normative detail §37.19 owns
// was computed by a helper no caller reached and the figure's property was
// unreadable. §37.58 detail 3 owns the property for a bit select, §37.19
// detail 1 for a var select, and §37.16 and §37.17 for a net bit and a var
// bit, and for every other net and variable, so each clause's rule answers for
// its own object; any other kind reports 0, its own clause owning what the
// property means for it.
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
