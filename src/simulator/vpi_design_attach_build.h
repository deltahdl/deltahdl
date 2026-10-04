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
enum class DataTypeKind : uint8_t;
struct Expr;
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

// §37.25: the typespec kind of a type of `kind`; 0 for a kind no typespec is
// drawn for here, such as a name standing for another type.
int VpiTypespecKind(DataTypeKind kind);

// §37.17: the object kind of a variable declared with a type of `kind`, a
// logic var for a type §37.17 draws no box of its own for.
int VpiDataTypeVariableKind(DataTypeKind kind);

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
// typedef it declares, and link each variable declared with one to it. Answers
// the compilation unit's typespecs by typedef name, since no scope object of
// the model holds them.
VpiObjectMap AttachTypespecs(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiAttachBuild& build);

// §37.28 details 1 and 2: make each value parameter a vpiParameter and each
// type parameter a vpiTypeParameter, each saying whether it is a localparam,
// and relate a type parameter to the typespec of the type it has, a typedef's
// among those its scope declares or `unit_typespecs`, the compilation unit's,
// which AttachTypespecs made and answered.
void AttachParameters(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiObjectMap& unit_typespecs,
                      const VpiAttachBuild& build);

// §37.17 details 4 and 6, §37.22: give each variable of the design its range
// objects and its leftmost bounds.
void AttachVariableRanges(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build);

// §37.58, §37.59: the expression object `expr` stands for, written in the
// instance whose objects `objects` keys under `prefix`; null for a kind of
// expression not modelled.
VpiObject* VpiInstanceExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const std::string& prefix, SimContext& ctx,
                                 const VpiAttachBuild& build);

// §37.12: give each instance an object per block its procedures write that is
// a scope, nested as the blocks are, each with the variables it declares.
void AttachBlockScopes(const RtlirDesign* design, const VpiObjectMap& objects,
                       const VpiAttachBuild& build);

// §37.7: give each interface instance a modport per modport its interface
// declares, each with an io decl per port it gives a direction, and §37.13:
// each io decl the vpiExpr of what the port connects to.
void AttachModports(const RtlirDesign* design, const VpiObjectMap& objects,
                    SimContext& ctx, const VpiAttachBuild& build);

}  // namespace delta
