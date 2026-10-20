#include <algorithm>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"

namespace delta {

int VpiAggregateNetSize(VpiHandle net) {
  VpiNetSizeQuery query;
  query.net_type = net->type;
  query.packed = net->packed;
  query.bit_width = net->size;
  query.member_count = static_cast<int>(
      std::ranges::count_if(net->children, VpiNetStructUnionMember));
  return VpiNetSize(query);
}

bool VpiNetIsScalarOrVector(bool scalar, VpiHandle net) {
  VpiNetScalarVectorQuery query;
  query.net_type = net->type;
  // A net's leftmost bounds are those of its leftmost packed dimension where
  // it declares one (§37.16 detail 26).
  query.has_packed_dimension = net->left_range != nullptr;
  query.packed = net->packed;
  // An enum net's base type is a scalar where it is a single bit.
  query.base_is_scalar = net->size == 1;
  query.base_is_vector = net->size > 1;
  // An array net answers as its element does.
  const auto kElement = std::ranges::find_if(
      net->children,
      [](const VpiObject* child) { return child->array_member; });
  if (kElement != net->children.end()) {
    query.element_is_scalar = VpiNetIsScalarOrVector(true, *kElement);
    query.element_is_vector = VpiNetIsScalarOrVector(false, *kElement);
  }
  return scalar ? VpiNetScalar(query) : VpiNetVector(query);
}

bool VpiIsPackedArrayNetElementType(int type) {
  switch (type) {
    case vpiStructNet:
    case vpiUnionNet:
    case vpiEnumNet:
    case vpiPackedArrayNet:
      return true;
    default:
      return false;
  }
}

}  // namespace delta
