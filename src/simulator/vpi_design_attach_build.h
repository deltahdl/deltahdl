#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/packed_range.h"

namespace delta {

class Arena;
class SimContext;
struct DataType;
struct RtlirDesign;
struct VpiObject;

// What an attach step that adds objects to the VPI model builds with:
// somewhere to allocate an object, a string to keep a name in for as long as
// the model lives, and the arena a constant's value lives in. VpiContext
// hands one to each step it runs, since the allocator is its own.
struct VpiAttachBuild {
  std::function<VpiObject*()> alloc;
  std::function<std::string_view(std::string)> keep;
  Arena& arena;
};

// The objects VpiContext keyed by flat name, which a step finds a declaration's
// object among.
using VpiObjectMap = std::unordered_map<std::string_view, VpiObject*>;

// An integer as the vpiIntConst constant a relation such as vpiIndex or
// vpiLeftRange reaches.
VpiObject* VpiIntConstant(int64_t value, const VpiAttachBuild& build);

// The packed dimensions of a value, outermost first, each a declared range.
using PackedDims = std::vector<PackedRange>;

// The number of bits `dims` span together.
int64_t PackedDimsWidth(const PackedDims& dims);

// §7.4.1: the packed dimensions `type` declares, outermost first, evaluated in
// the scope `ctx` has set, where they account for all `width` bits. A packed
// array of packed structs or unions declares the outer dimensions alone, and
// the elements' bits are indexed below them as each element's own [n-1:0]
// (§7.2.1). Null where the declaration writes none, or where the width does not
// divide among them.
std::optional<PackedDims> DeclaredPackedDims(const DataType* type,
                                             uint32_t width, SimContext& ctx);

// The packed dimensions as the declaration wrote them, without the element
// range DeclaredPackedDims adds below a packed array of aggregates; none where
// it wrote none.
PackedDims WrittenPackedDims(const DataType* type, SimContext& ctx);

// §37.16, §37.17: give each vector net its net bits and each packed variable
// its var bits.
void AttachVectorBits(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build);

// §37.17 details 2, 18 and 26: hang each element of a fixed array var from
// the array, through a subarray per outer index of a multidimensional one.
void AttachArrayElements(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiAttachBuild& build);

// §37.17 details 3, 17 and 26: give each unpacked struct or union var a member
// variable per field.
void AttachStructMembers(const RtlirDesign* design, const VpiObjectMap& objects,
                         SimContext& ctx, const VpiAttachBuild& build);

// §37.25, §37.26, §37.85 detail 5 and §37.17: give each scope a typespec per
// typedef it declares, and link each variable declared with one to it.
void AttachTypespecs(const RtlirDesign* design, const VpiObjectMap& objects,
                     const VpiAttachBuild& build);

// §37.17 details 4 and 6, §37.22: give each variable of the design its range
// objects and its leftmost bounds.
void AttachVariableRanges(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build);

}  // namespace delta
