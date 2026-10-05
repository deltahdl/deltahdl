#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/packed_range.h"

namespace delta {

class Arena;
class SimContext;
struct DataType;
enum class DataTypeKind : uint8_t;
struct Expr;
struct RtlirDesign;
struct RtlirModule;
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

// §37.17, §37.27 and §37.29: the object kind of a variable declared with a
// type of `kind`, a logic var for a type §37.17 draws no box of its own for.
// A module's variables, a block's and a struct's members take their kinds
// from it alike.
int VpiDataTypeVariableKind(DataTypeKind kind);

// §6.18 with §8.3: the object kind of a variable an instance of `mod` declares
// with a type standing for `name`: a class var for a class the module or the
// compilation unit declares, a built-in class or a typedef whose chain of
// names ends in a class, and for any other typedef the kind of the type at the
// end of its chain; a logic var for a name nothing resolves.
int VpiNamedTypeVariableKind(const RtlirDesign& design, const RtlirModule& mod,
                             std::string_view name);

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

// §37.42: a system task or function an application registered, as a call
// that names it finds it: the systf object vpi_register_systf returned for it
// and the vpiSysTask or vpiSysFunc type it was registered with. A name no
// registration claims finds a null object and a zero type.
struct VpiRegisteredSystf {
  VpiObject* object = nullptr;
  int type = 0;
};

// §37.42 detail 3: the model's object for each call statement of a run, keyed
// by the call the statement writes and the flat name of the instance writing
// it, since every instance of a module carries the one parsed call.
using VpiCallSiteObjects =
    std::map<std::pair<const Expr*, std::string>, VpiObject*>;

// What the procedure walk builds a call statement with: the run, which an
// argument's value is read through; the
// registration a system call's name resolves to; and the record of the call
// statements made, which a run's invocation of a registered system task finds
// its own call among.
struct VpiCallBuild {
  SimContext& ctx;
  std::function<VpiRegisteredSystf(std::string_view)> systf;
  VpiCallSiteObjects& sites;
};

// §37.63: give each instance a process per procedure it declares, reaching the
// statement it runs; §37.12: an object per block its procedures write that is
// a scope, nested as the blocks are, each with the variables it declares;
// §37.62: an event statement per trigger, and §37.42: a call statement per
// task, method task and system task call, each hung from the scope it stands
// in.
void AttachProcedures(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiCallBuild& calls, const VpiAttachBuild& build);

// §37.7: give each interface instance a modport per modport its interface
// declares, each with an io decl per port it gives a direction, and §37.13:
// each io decl the vpiExpr of what the port connects to.
void AttachModports(const RtlirDesign* design, const VpiObjectMap& objects,
                    SimContext& ctx, const VpiAttachBuild& build);

}  // namespace delta
