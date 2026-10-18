#include "simulator/vpi_typespec_shapes.h"

#include <utility>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

void VpiTypespecShapes::Shape(VpiObject* typespec,
                              const std::vector<VpiTypespecDim>& dims,
                              VpiObject* base) {
  const Written& written = written_[typespec] = {dims, base};
  const VpiTypespecDim& outermost = dims.front();
  if (outermost.unpacked) {
    typespec->type = vpiArrayTypespec;
  } else if (base->type == vpiBitTypespec || base->type == vpiLogicTypespec) {
    typespec->type = base->type;
  } else {
    typespec->type = vpiPackedArrayTypespec;
  }
  typespec->array_type = outermost.array_type;
  typespec->decl_vector = !outermost.unpacked;
  const std::vector<const VpiTypespecDim*> kRanged = Ranged(written);
  for (const VpiTypespecDim* dim : kRanged) {
    typespec->children.push_back(VpiRangeObject(typespec, dim->bounds, build_));
  }
  typespec->left_range = typespec->children.front()->left_range;
  typespec->right_range = typespec->children.front()->right_range;
  if (outermost.index_typespec != nullptr) {
    if (outermost.index_typespec->parent == nullptr) {
      outermost.index_typespec->parent = typespec;
    }
    typespec->children.push_back(outermost.index_typespec);
  }
  typespec->inner_typespec =
      Unnamed(typespec, {dims.begin() + 1, dims.end()}, base);
}

VpiObject* VpiTypespecShapes::Unnamed(VpiObject* parent,
                                      const std::vector<VpiTypespecDim>& dims,
                                      VpiObject* base) {
  if (dims.empty()) return base;
  VpiObject* typespec = build_.alloc();
  typespec->parent = parent;
  Shape(typespec, dims, base);
  return typespec;
}

void VpiTypespecShapes::Share(VpiObject* alias, VpiObject* aliased) {
  alias->children = aliased->children;
  alias->left_range = aliased->left_range;
  alias->right_range = aliased->right_range;
  alias->array_type = aliased->array_type;
  alias->inner_typespec = aliased->inner_typespec;
  alias->decl_vector = aliased->decl_vector;
  alias->packed = aliased->packed;
  alias->tagged = aliased->tagged;
  alias->soft = aliased->soft;
  auto it = written_.find(aliased);
  if (it == written_.end()) return;
  Written copied = it->second;
  written_[alias] = std::move(copied);
}

std::vector<const VpiTypespecDim*> VpiTypespecShapes::Ranged(
    const Written& written) const {
  std::vector<const VpiTypespecDim*> ranged;
  const bool kUnpacked = written.dims.front().unpacked;
  for (const Written* at = &written;;) {
    for (const VpiTypespecDim& dim : at->dims) {
      if (dim.unpacked != kUnpacked) return ranged;
      ranged.push_back(&dim);
    }
    auto it = written_.find(at->base);
    if (it == written_.end()) return ranged;
    at = &it->second;
  }
}

}  // namespace delta
