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
struct ClassDecl;
struct DataType;
enum class DataTypeKind : uint8_t;
struct Expr;
struct ModuleItem;
struct RtlirDesign;
struct RtlirModule;
struct Stmt;
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

// §7.4.2: one unpacked dimension `dim` as the declaration wrote it, a range
// `[left:right]` or a size `[n]` standing for `[0:n-1]`, evaluated in the
// scope `ctx` has set. Empty for a dynamic, queue or associative dimension,
// and for a size that is not positive.
std::optional<PackedRange> WrittenUnpackedDim(const Expr* dim, SimContext& ctx);

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

// §37.3.1 with §37.10 detail 5: the full name of `name` declared in `scope`,
// written after an instance's name and a dot or after the `::` that ends a
// package's full name, and under `$unit::` where no scope object holds it.
std::string VpiScopedFullName(const VpiObject* scope, std::string_view name);

// §37.41: the task or function object made for each task or function
// declaration, keyed by the declaration and the flat name of the scope it was
// made in: an instance's path, a package's name, or "$unit" for the
// compilation unit.
using VpiSubroutineObjects =
    std::map<std::pair<const ModuleItem*, std::string>, VpiObject*>;

// §37.41: give each module instance, generate block instance and package a
// task or function per one it declares, and make one per task or function of
// the compilation unit, each named, full-named, reporting its lifetime and
// holding its io decls, its return variable and the variables its body
// declares, a return variable's width read in the run `ctx`. Answers the
// objects made.
VpiSubroutineObjects AttachSubroutines(const RtlirDesign* design,
                                       const VpiObjectMap& objects,
                                       SimContext& ctx,
                                       const VpiAttachBuild& build);

// §37.42: the task or function a call resolves to, its declaration and the
// object made for it, null where none was made; a null declaration where the
// call resolves to none.
struct VpiCalledSubroutine {
  const ModuleItem* decl = nullptr;
  VpiObject* object = nullptr;
};

// Where a call is written: the design; the module of the instance writing it
// and the flat name the instance's objects are keyed under; the scope object
// it stands in, the instance or a block of it; and the tasks and functions
// made.
struct VpiCallSite {
  const RtlirDesign& design;
  const RtlirModule& mod;
  const std::string& prefix;
  const VpiObject* scope;
  const VpiSubroutineObjects& made;
};

// §26.2: the task or function the package `package` declares under `name`.
VpiCalledSubroutine VpiPackageSubroutine(const RtlirDesign& design,
                                         std::string_view package,
                                         std::string_view name,
                                         const VpiSubroutineObjects& made);

// The task or function a call of `name` written at `site` resolves to: one a
// generate block enclosing it declares, the innermost first (§27.4), one the
// instance's module or the compilation unit declares, or, by §26.3, one the
// module imports from a package by its name or with a wildcard.
VpiCalledSubroutine VpiNamedSubroutine(const VpiCallSite& site,
                                       std::string_view name);

// The same for the callee `callee` of a call: a name alone, or a package's
// subroutine behind the package's name, `p::f`; none for any other callee.
VpiCalledSubroutine VpiCalleeSubroutine(const VpiCallSite& site,
                                        const Expr& callee);

// §37.42: the task or function object a call's callee resolves to from where
// the call is written, null where none was made.
using VpiCalleeResolver = std::function<VpiObject*(const Expr& callee)>;

// The resolver of the callees of calls written at `site`.
VpiCalleeResolver VpiCalleesAt(const VpiCallSite& site);

// §37.31: the class defn made for each class declaration, keyed by the
// declaration and the flat name of the scope it was made in: an instance's
// path, a package's name, or "$unit" for the compilation unit.
using VpiClassDefnObjects =
    std::map<std::pair<const ClassDecl*, std::string>, VpiObject*>;

// §37.31: give each module instance and each package a class defn per class it
// declares, and make one per class of the compilation unit, reached with a
// NULL reference, each with its properties and methods; and details 5 and 6:
// give each derived class its extends object and hang it from its base's
// derived classes. Answers the class defns it made.
VpiClassDefnObjects AttachClassDefinitions(const RtlirDesign* design,
                                           const VpiObjectMap& objects,
                                           SimContext& ctx,
                                           const VpiAttachBuild& build);

// §37.17 details 4 and 6, §37.22: give each variable of the design its range
// objects and its leftmost bounds.
void AttachVariableRanges(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build);

// §37.17 details 4 and 6 for a variable a task or function declares (§37.41):
// give `obj` a range object per dimension it was declared with, the unpacked
// dimensions `unpacked_dims` where it writes any and otherwise the packed
// dimensions `type` writes, and the leftmost one's bounds.
void AttachDeclaredRanges(VpiObject* obj, const DataType& type,
                          const std::vector<Expr*>& unpacked_dims,
                          SimContext& ctx, const VpiAttachBuild& build);

// §37.58, §37.59: the expression object `expr` stands for, written in the
// instance whose objects `objects` keys under `prefix`; null for a kind of
// expression not modelled.
VpiObject* VpiInstanceExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const std::string& prefix, SimContext& ctx,
                                 const VpiAttachBuild& build);

// §37.58, §37.59: the expression object `expr` stands for, written at `site`
// in the instance whose objects `objects` keys, a name in it resolving first
// to a declaration of the blocks around the site (§23.9) and a func call in it
// reaching the function its callee resolves to there (§37.42); null for a kind
// of expression not modelled.
VpiObject* VpiCallSiteExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const VpiCallSite& site, SimContext& ctx,
                                 const VpiAttachBuild& build);

// §9.7, §15.3 and §15.4: the kind of tf call a call of the method `method` of
// the built-in class `cls` is, vpiMethodTaskCall or vpiMethodFuncCall, zero
// for none.
int VpiBuiltInClassCallKind(std::string_view cls, std::string_view method);

// Whether `name` is a system function the standard defines, which a statement
// calling it calls as a function.
bool VpiIsBuiltInSystemFunction(std::string_view name);

// What the objects one statement reaches are built with: the build; the
// expression object an expression the statement writes stands as, null for
// one not modelled; and the object a statement it holds stands as, hung from
// the object given and walked for the objects it holds in turn, null for one
// the run builds no object for; and the kind of the first index variable of a
// foreach loop over the array an expression names (§12.7.3).
struct VpiStmtBuild {
  const VpiAttachBuild& build;
  std::function<VpiObject*(const Expr*)> expression;
  std::function<VpiObject*(const Stmt*, VpiObject*)> statement;
  std::function<int(const Expr*)> index_kind;
};

// §37.64 to §37.68, §37.70 to §37.72 and §37.74 to §37.79: the kind of object
// `stmt` stands as when it is an assignment, an event or delay control, an
// assign, deassign, force or release, an if or if-else, a case, a forever,
// while, repeat, do-while, for or foreach loop, a wait, wait fork or ordered
// wait, or a disable or disable fork (§37.77); 0 for a statement of another
// kind.
int VpiBuiltStmtKind(const Stmt& stmt);

// The objects `obj`, made for `stmt` with the kind above, reaches: the
// expressions its figure draws and the statements it holds, each built
// through `with`.
void VpiFillStmt(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with);

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
// argument's value is read through; the registration a system call's name
// resolves to; the record of the call statements made, which a run's
// invocation of a registered system task finds its own call among; the
// class defns made, whose methods a method call reaches; and the tasks and
// functions made, which a task or func call reaches.
struct VpiCallBuild {
  SimContext& ctx;
  std::function<VpiRegisteredSystf(std::string_view)> systf;
  VpiCallSiteObjects& sites;
  const VpiClassDefnObjects& classes;
  const VpiSubroutineObjects& subroutines;
};

// §37.63: give each instance a process per procedure it declares, reaching the
// statement it runs; §37.12: an object per block its procedures write, nested
// as the blocks are, each with the variables it declares; §37.62: an event
// statement per trigger, §37.42: a call statement per task, method task and
// system task call, and an object per statement VpiBuiltStmtKind names, each
// hung from the block or statement it stands in.
void AttachProcedures(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiCallBuild& calls, const VpiAttachBuild& build);

// §37.7: give each interface instance a modport per modport its interface
// declares, each with an io decl per port it gives a direction, and §37.13:
// each io decl the vpiExpr of what the port connects to.
void AttachModports(const RtlirDesign* design, const VpiObjectMap& objects,
                    SimContext& ctx, const VpiAttachBuild& build);

}  // namespace delta
