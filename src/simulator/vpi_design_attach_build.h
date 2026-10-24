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
#include "common/source_loc.h"
#include "elaborator/rtlir_attribute.h"

namespace delta {

class Arena;
class SimContext;
struct ClassDecl;
struct ClassMember;
struct ConstraintDistItem;
struct DataType;
struct EventExpr;
enum class DataTypeKind : uint8_t;
enum class StmtKind : uint8_t;
enum class TokenKind : uint16_t;
struct Expr;
struct ModuleDecl;
struct ModuleItem;
struct PackageDecl;
struct PropertyExprNode;
struct SeqLinearBody;
struct RtlirAssertion;
struct RtlirDesign;
struct RtlirImport;
struct RtlirModule;
struct RtlirNet;
struct RtlirPort;
struct RtlirVariable;
struct Stmt;
struct UdpDecl;
struct VpiDeferredCall;
struct VpiObject;

// What an attach step that adds objects to the VPI model builds with:
// somewhere to allocate an object, a string to keep a name in for as long as
// the model lives, and the arena a constant's value lives in. VpiContext
// hands one to each step it runs, since the allocator is its own.
struct VpiAttachBuild {
  std::function<VpiObject*()> alloc;
  std::function<std::string_view(std::string)> keep;
  Arena& arena;
  // §37.42: where a call an expression written outside every procedure makes
  // is held until it can be shaped (VpiShapeDeferredCalls); null where such a
  // call is left as it is built.
  std::vector<VpiDeferredCall>* deferred_calls = nullptr;
};

// What keeps a name for as long as the model lives, answering the kept copy.
using VpiNameKeeper = std::function<std::string_view(std::string)>;

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

// §37.16 (figure) and detail 1: the object kind of a net the declaration `net`
// makes, by the data type it was declared with -- a logic net for a type the
// figure draws no box of its own for.
int VpiNetObjectKind(const RtlirNet& net);

// §37.16 (figure): tell each net of `design`, which is not null, the kind its
// data type makes it, and each net of an array net the kind of its element
// type.
void RecordNetObjectKinds(const RtlirDesign* design,
                          const VpiObjectMap& objects);

// §6.18 with §8.3: the object kind of a variable an instance of `mod` declares
// with a type standing for `name`: a class var for a class the module or the
// compilation unit declares, a built-in class or a typedef whose chain of
// names ends in a class, and for any other typedef the kind of the type at the
// end of its chain; a logic var for a name nothing resolves.
int VpiNamedTypeVariableKind(const RtlirDesign& design, const RtlirModule& mod,
                             std::string_view name);

// §6.18 with §8.3 and §26.3: the same for a variable the package `package`
// declares, or the compilation unit where `package` is null: a class var for a
// class the package or the compilation unit declares, a built-in class or a
// typedef whose chain of names ends in a class, and for any other typedef the
// kind of the type at the end of its chain, a package's typedef found under
// its qualified name `p::t`; a logic var for a name nothing resolves.
int VpiPackageNamedTypeVariableKind(const RtlirDesign& design,
                                    const PackageDecl* package,
                                    std::string_view name);

// §26.2: the classes the package `package` declares, in the order written.
std::vector<ClassDecl*> VpiPackageClasses(const PackageDecl& package);

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

// §38.16 and §38.35: give the array var `array`, standing for a class's
// property (§37.31, §37.33), which no element of the run is kept under, the
// indices each of its unpacked dimensions `dims` writes, left first, as a
// module's array var has them, through which a select of a select is told from
// a select of an element (§37.19); none where a dimension is not fixed.
void VpiRecordWrittenDims(VpiObject& array, const std::vector<Expr*>& dims,
                          SimContext& ctx);

// §37.16 (figure): the nets `mod` declares - those its body declares, and those
// its ANSI ports declare, which stand in no list of the body's - each as a
// declaration of its name, data type and dimensions.
std::vector<RtlirNet> VpiDeclaredNets(const RtlirModule& mod);

// §37.24 (figure) with §6.6.8: whether `net` was declared a generic
// interconnect, which stands as an interconnect net or array whatever net type
// a port connection merged it into (§23.3.3.7.1).
bool VpiNetIsInterconnect(const RtlirNet& net);

// §37.17 (figure): the variables `mod` declares - those its body declares, and
// those its ANSI variable ports declare, which stand in no list of the body's
// unless their type is a structure or union - each as a declaration of its
// name, data type and dimensions.
std::vector<RtlirVariable> VpiDeclaredVariables(const RtlirModule& mod);

// §37.16 (figure): the flat keys of the nets the declaration `net` makes in
// the instance at `prefix`, each a net holding a value: the net itself, or of
// an array net the nets it holds, which the run keys under `n[i]` for a
// one-dimensional array and makes for no other.
std::vector<std::string> VpiDeclaredNetKeys(const RtlirNet& net,
                                            const std::string& prefix);

// §37.16, §37.17: give each vector net its net bits and each packed variable
// its var bits.
void AttachVectorBits(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build);

// §37.17 details 2, 18 and 26: hang each element of a fixed array var from
// the array, through a subarray per outer index of a multidimensional one,
// and (§37.16 details 1 and 2) each net of an array net from the array net.
void AttachArrayElements(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiAttachBuild& build);

// §37.17 details 3, 17 and 26: give each unpacked struct or union var a member
// variable per field.
void AttachStructMembers(const RtlirDesign* design, const VpiObjectMap& objects,
                         SimContext& ctx, const VpiAttachBuild& build);

// §26.3: the typespec of the typedef `name` a package declares that one of
// `imports` makes visible, among those AttachTypespecs answered, `answered`,
// under the package's name and "::"; null where no import reaches one.
VpiObject* VpiImportedTypespec(std::string_view name,
                               const std::vector<RtlirImport>& imports,
                               const VpiObjectMap& answered);

// §37.28 details 1 and 2: make each value parameter a vpiParameter and each
// type parameter a vpiTypeParameter, each saying whether it is a localparam,
// and relate a type parameter to the typespec of the type it has, a typedef's
// among those its scope declares or `unit_typespecs`, the compilation unit's,
// which AttachTypespecs made and answered. §37.3.3: each reports the line
// and file its declaration was written at, which `ctx`'s source description
// resolves.
void AttachParameters(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiObjectMap& unit_typespecs, SimContext& ctx,
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
// The module, interface or program the compilation unit declares under
// `name`, an empty declaration, declaring nothing, for none.
const ModuleDecl& ElementDeclNamed(const RtlirDesign& design,
                                   std::string_view name);

VpiSubroutineObjects AttachSubroutines(const RtlirDesign& design,
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
  // §27.4: the prefixes of the generate block instances the site stands in,
  // innermost last, whose declarations a name finds ahead of the instance's;
  // null where it stands in none.
  const std::vector<std::string_view>* gen_prefixes = nullptr;
  // §37.42: what makes the call `call`, a call of a subroutine or a method
  // written in an expression at the site, into `made` as a call statement
  // written there is made, true where it does; none where the site stands in
  // no procedure.
  std::function<bool(const Expr& call, VpiObject* made)> shape_call = nullptr;
  // §26.2: the package the site stands in, whose declarations alone a name
  // finds; empty for a site of an instance or the compilation unit.
  std::string_view package = {};
  // §16.8 and §16.12: the object holding the stand-ins for the formals of the
  // sequence or property declaration whose body the site is in
  // (VpiFormalNames), which a name finds ahead of the blocks around `scope`;
  // null for a site in no such body.
  const VpiObject* formals = nullptr;
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

// §26.3: whether `name` is written through a package's path, `p::f`, both the
// package's name and the item's a plain identifier.
bool VpiIsPackageScopedName(const Expr& name);

// §37.42: the task or function object a call's callee resolves to from where
// the call is written, null where none was made.
using VpiCalleeResolver = std::function<VpiObject*(const Expr& callee)>;

// The resolver of the callees of calls written at `site`.
VpiCalleeResolver VpiCalleesAt(const VpiCallSite& site);

// §37.31: the class defn made for each class declaration, keyed by it and
// the flat name of the scope it was made in: an instance's path, a generate
// block instance's full name, a package's name, or "$unit".
using VpiClassDefnObjects =
    std::map<std::pair<const ClassDecl*, std::string>, VpiObject*>;

// §37.42: where a call a class's constraint writes stands, by the class defn:
// the module or package declaring the class, whose declarations its callee is
// found among, which a class obj of the class keeps, standing as the call's
// scope itself (§37.12).
struct VpiClassCallSite {
  const RtlirModule* mod = nullptr;
  std::string_view package;
};
using VpiClassCallSites =
    std::unordered_map<const VpiObject*, VpiClassCallSite>;

// §37.31: give each module instance and each package a class defn per class it
// declares, and make one per class of the compilation unit, reached with a
// NULL reference, each with its properties and methods; and details 5 and 6:
// give each derived class its extends object and hang it from its base's
// derived classes. Answers the class defns it made, and records in `sites`
// where each one's calls stand.
VpiClassDefnObjects AttachClassDefinitions(const RtlirDesign* design,
                                           const VpiObjectMap& objects,
                                           SimContext& ctx,
                                           const VpiAttachBuild& build,
                                           VpiClassCallSites& sites);

// §37.33 detail 5: the class defn among `defns` the class type `written`
// names from the scope keyed under `prefix`: the package's class where it
// names its package, and otherwise one the scope declares, then the
// compilation unit's, then a package's. Null where none does, as for a
// built-in class (§37.32).
VpiObject* VpiNamedClassDefn(const VpiClassDefnObjects& defns,
                             std::string_view written,
                             const std::string& prefix);

// §37.25, §37.26, §37.85 detail 5 and §37.17: give each scope a typespec per
// typedef it declares, with the ranges, elements, members and base its type
// makes, a class's reaching its class defn among `classes`, its dimensions
// evaluated in the instance declaring it through `ctx`; and link each
// variable declared with one to it. Answers the compilation unit's typespecs
// by typedef name, since no scope object of the model holds them, and each
// package's by the package's name, "::" and the typedef's name, for a scope
// importing them to reach.
VpiObjectMap AttachTypespecs(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiClassDefnObjects& classes,
                             SimContext& ctx, const VpiAttachBuild& build);

// §37.33 detail 5 and §37.32 detail 1: give each class var an instance
// declares the class typespec of the class it was declared with: the typespec
// of the class specialization the run `ctx` gave it, which that class's defn
// among `defns` holds, and otherwise one reaching that defn where one was
// made.
void AttachClassVarTypespecs(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiClassDefnObjects& defns, SimContext& ctx,
                             const VpiAttachBuild& build);

// §37.17 details 4 and 6, §37.16 detail 26, §37.22: give each variable and
// each net of the design its range objects and its leftmost bounds.
void AttachVariableAndNetRanges(const RtlirDesign& design,
                                const VpiObjectMap& objects, SimContext& ctx,
                                const VpiAttachBuild& build);

// §37.17 details 4 and 6 for a variable a task or function declares (§37.41):
// give `obj` a range object per dimension it was declared with, the unpacked
// dimensions `unpacked_dims` where it writes any and otherwise the packed
// dimensions `type` writes, and the leftmost one's bounds.
void AttachDeclaredRanges(VpiObject* obj, const DataType& type,
                          const std::vector<Expr*>& unpacked_dims,
                          SimContext& ctx, const VpiAttachBuild& build);

// §37.16, §37.17: the net bit or var bit of `root` at `offset` above the least
// significant end of its storage; null where it has none.
VpiObject* VpiBitAtOffset(const VpiObject& root, int64_t offset);

// §37.59: the vpiOpType of a binary operator, and 0 for one the table does
// not hold. An event expression passed as an actual (§16.12.18) joins its
// events with `or` and guards one with `iff`, as §9.4.2 writes them.
int VpiBinaryOpType(TokenKind op);

// §37.59: the vpiOpType of a prefix unary operator, and 0 for one the table
// does not hold. An event expression passed as an actual (§16.12.18) writes
// its edge as one.
int VpiUnaryOpType(TokenKind op);

// §11.4.2: the vpiOpType of the increment or decrement operator `op`, the
// post forms for `i++` and `i--` written `postfix`, the pre forms for `++i`
// and `--i`; 0 for an operator that is neither.
int VpiIncDecOpType(TokenKind op, bool postfix);

// §37.61 (figure): whether an object of `type` can prefix an expression - a
// class var, a virtual interface var or a clocking block.
bool VpiIsDynamicPrefixHolderType(int type);

// §37.59: gives an operation, a part select or an indexed part select built
// with no size its self-determined width (§11.6.1), read off its operands and
// its range; any other expression is left as it is.
void VpiSizeExpression(VpiObject* expr);

// `scope` where it is given, and otherwise the instance `objects` holds under
// `instance`; null for neither.
const VpiObject* VpiScopeOrInstance(const VpiObject* scope,
                                    const VpiObjectMap& objects,
                                    const std::string& instance);

// §37.59 details 3 and 5: `op`, the cast operation `cast` stands as, related
// to the typespec of the type it casts to - a built-in type a keyword names,
// a typedef `from`, or a scope around it, declares, or for a size, signing or
// const cast (§6.24.1) one made from its operand's type, a size cast's being
// as wide as the value `width` holds. Answers `op`.
VpiObject* VpiTypedCast(VpiObject* op, const Expr& cast, const VpiObject* from,
                        const VpiObject* width,
                        const std::function<VpiObject*()>& alloc);

// §14.3 with §23.9: the clocking block named `name` that `scope`, or a scope
// around it, declares - from the instance `objects` holds under `instance`
// where no scope is given; null for none.
VpiObject* VpiClockingBlockAround(const VpiObject* scope,
                                  const VpiObjectMap& objects,
                                  const std::string& instance,
                                  std::string_view name);

// §37.61 detail 1: the simple expression written through `holder`, one of the
// three, as `written`: a ref obj named as written whose vpiPrefix is `holder`.
// Which object it stands for is fixed only as the run goes, so it holds none.
VpiObject* VpiPrefixedReference(VpiObject* holder, std::string_view written,
                                const std::function<VpiObject*()>& alloc,
                                const VpiNameKeeper& keep);

// §37.58, §37.59: the expression object `expr` stands for, written in the
// instance whose objects `objects` keys under `prefix`; null for a kind of
// expression not modelled.
VpiObject* VpiInstanceExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const std::string& prefix, SimContext& ctx,
                                 const VpiAttachBuild& build);

// §37.42 with §37.12: where a call written outside every procedure stands:
// the scope its vpiScope reaches - the instance, gen scope, clocking block,
// package or class defn it is written in - and the module whose declarations
// its callee is found among, null where it stands in no module, or the
// package, for a call a package or a class it declares writes (§26.2).
struct VpiCallStand {
  VpiObject* scope;
  const RtlirModule* mod = nullptr;
  std::string_view package = {};
};

// Where the names of an expression written in an instance resolve: the
// instance, whose objects `objects` keys under `prefix`, and the generate
// block instances it stands in, by their prefixes, innermost last, whose
// declarations a name finds first (§27.4).
struct VpiExprNames {
  const VpiObjectMap& objects;
  const std::string& prefix;
  const std::vector<std::string_view>& gen_prefixes;
  // The object whose declarations, and those of the objects above it up to
  // the instance, a name finds first (§23.9); null for none.
  const VpiObject* scope = nullptr;
  // §37.83: the attributes elaboration resolved on the operators written
  // where the expression is, its instance's or the design's; null for none.
  const RtlirNodeAttributes* attrs = nullptr;
  // §37.42: where a call the expression makes stands, which makes it a tf
  // call as a procedure's is once shaped; null to leave it unshaped.
  const VpiCallStand* stand = nullptr;
};

// The same of an expression written in the generate block instances `names`
// carries.
VpiObject* VpiGenBlockExpression(const Expr* expr, const VpiExprNames& names,
                                 SimContext& ctx, const VpiAttachBuild& build);

// §37.42: a call `call`, made as `made` where `stand` says, with the flat name
// of the instance and the generate block instances its names resolve in, held
// for VpiShapeDeferredCalls.
struct VpiDeferredCall {
  const Expr* call;
  VpiObject* made;
  VpiCallStand stand;
  std::string prefix;
  std::vector<std::string_view> gen_prefixes;
};

// §37.58, §37.59: the expression object `expr` stands for, written at `site`
// in the instance whose objects `objects` keys, a name in it resolving first
// to a declaration of the blocks around the site (§23.9) and a func call in it
// reaching the function its callee resolves to there (§37.42); null for a kind
// of expression not modelled.
VpiObject* VpiCallSiteExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const VpiCallSite& site, SimContext& ctx,
                                 const VpiAttachBuild& build);

// §37.64: the right side of an assignment, `expr`, and the object its left
// side stands as, `target`.
struct VpiAssignedSide {
  const Expr* expr;
  const VpiObject* target;
};

// §37.64 with §37.59 detail 6: VpiCallSiteExpression's object for the right
// side of `side`, a keyed assignment pattern ordered by the members or
// elements of its target.
VpiObject* VpiCallSiteAssignedExpression(const VpiAssignedSide& side,
                                         const VpiObjectMap& objects,
                                         const VpiCallSite& site,
                                         SimContext& ctx,
                                         const VpiAttachBuild& build);

// §9.7, §15.3 and §15.4: the kind of tf call a call of the method `method` of
// the built-in class `cls` is, vpiMethodTaskCall or vpiMethodFuncCall, zero
// for none. A built-in class has the built-in methods every class has too.
int VpiBuiltInClassCallKind(std::string_view cls, std::string_view method);

// §18.6.1, §18.6.2, §18.8, §18.9 and §18.13.3 to §18.13.5: whether `method` is
// one of the built-in methods every class has without declaring it, randomize,
// pre_randomize, post_randomize, rand_mode, constraint_mode, srandom,
// get_randstate and set_randstate, each a function.
bool VpiIsClassBuiltInMethod(std::string_view method);

// §18.8 and §18.9: the kind of tf call a call of `method` applied to a member
// of a class is where the member's own class declares no such method: the
// built-in function rand_mode of a random variable, or constraint_mode of a
// constraint block, vpiMethodFuncCall; zero for any other method.
int VpiMemberBuiltInCallKind(std::string_view method);

// The kind of value a built-in method is called on: a string (§6.16), an enum
// (§6.19.5), a fixed-size, dynamic or associative array or a queue (§7.4,
// §7.5, §7.8, §7.10), a covergroup instance (§19.8), a named event (§15.5.3),
// or none of them.
enum class VpiBuiltInHolder : uint8_t {
  kNone,
  kString,
  kEnum,
  kFixedArray,
  kDynamicArray,
  kAssocArray,
  kQueue,
  kCovergroup,
  kEvent,
};

// What the objects one statement reaches are built with: the build; the
// expression object an expression the statement writes stands as, null for
// one not modelled; and the object a statement it holds stands as, hung from
// the object given and walked for the objects it holds in turn, null for one
// the run builds no object for; the kind of the first index variable of a
// foreach loop over the array an expression names (§12.7.3); the expression
// object of an expression assigned to the object given, whose members or
// elements order a keyed pattern (§37.59 detail 6); and the property decl a
// package declares under a name an import of the scope makes visible (§26.3),
// null for none.
struct VpiStmtBuild {
  const VpiAttachBuild& build;
  std::function<VpiObject*(const Expr*)> expression;
  std::function<VpiObject*(const Stmt*, VpiObject*)> statement;
  std::function<int(const Expr*)> index_kind;
  std::function<VpiObject*(const Expr*, const VpiObject*)> assigned;
  // §37.51 and §37.54: the declaration of the type given, a property decl or a
  // sequence decl, that a property or sequence named `name` where the
  // statement stands instantiates, written through the package path given
  // where it is not empty, null where the name declares none; null for a
  // builder nothing is instantiated through.
  std::function<VpiObject*(int, std::string_view, std::string_view)>
      assertion_decl;
};

// §37.64 to §37.68, §37.70 to §37.72 and §37.74 to §37.79: the kind of object
// `stmt` stands as when it is an assignment, an event or delay control, an
// assign, deassign, force or release, an if or if-else, a case, a forever,
// while, repeat, do-while, for or foreach loop, a wait, wait fork or ordered
// wait, a disable or disable fork (§37.77), or an assertion: an immediate
// one, or a concurrent one embedded in procedural code (§37.50), or an expect
// statement (§37.73); 0 for a statement of another kind.
int VpiBuiltStmtKind(const Stmt& stmt);

// §37.60: the kind of an atomic statement of `kind` that carries nothing but
// its label, a break, a continue or a null statement; 0 for another kind.
int VpiBareAtomicKind(StmtKind kind);

// §37.65 with §9.4.2: the condition an event control written over `events` is
// written over, the events joined by event or operations; null where an event
// is not modelled.
VpiObject* VpiEventCondition(const std::vector<EventExpr>& events,
                             const VpiStmtBuild& with);

// §37.50: give the concurrent assertion `obj` the clock it is evaluated on,
// the one the statement carrying its property, `property`, resolved, and
// whether that clock was inferred.
void VpiFillAssertionClock(VpiObject* obj, const Stmt& property,
                           const VpiStmtBuild& with);

// §37.52: the property spec `property` carries, hung from `holder` with its
// clock, its disable condition and the property expression of a Boolean
// property; null where the spec was not read.
VpiObject* VpiMakePropertySpec(VpiObject* holder, const Stmt& property,
                               const VpiStmtBuild& with);

// §37.52: what a property spec is made of: the clock written or inferred for
// it, its disable condition, and the tree of its property, null where the
// parser read none.
struct VpiPropertySpecParts {
  const std::vector<EventExpr>& clock;
  const Expr* disable = nullptr;
  const PropertyExprNode* property = nullptr;
};

// §37.54: the sequence expr the linear body `body` stands for: its operands
// joined by cycle delays and repeated, its intersects, conjuncts and
// alternatives, its throughouts and its within, its operands' match items,
// under first_match where written, each built through `with`; a chain whose
// operands name clocks a multiclock sequence expr (§37.56), the clock
// `flowing` into it, where known, its leading run's; null for a body holding
// match items inside a first_match, or clocks beside an operator.
VpiObject* VpiSequenceExprObject(const SeqLinearBody& body,
                                 const VpiStmtBuild& with,
                                 const std::vector<EventExpr>* flowing);

// §37.52: the property expr the property tree `node` stands for: the
// expression of a Boolean, or the operation of a property operator (detail
// 2) over its operands, each built through `with`, the clock `flowing` into
// it, where known, flowing on to the sequences among them (§16.13.3); null
// for a form not built.
VpiObject* VpiPropertyExprObject(const PropertyExprNode* node,
                                 const VpiStmtBuild& with,
                                 const std::vector<EventExpr>* flowing);

// §37.52: the property spec of `parts`, hung from `holder`.
VpiObject* VpiMakePropertySpecOf(VpiObject* holder,
                                 const VpiPropertySpecParts& parts,
                                 const VpiStmtBuild& with);

// §37.22: a range object under `parent` of the dimension `bounds`, an empty
// range where it has none.
VpiObject* VpiRangeObject(VpiObject* parent,
                          const std::optional<PackedRange>& bounds,
                          const VpiAttachBuild& build);

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
  // §38.37.1: the kind of value a registered system function returns, zero
  // for a system task.
  int sysfunctype = 0;
};

// §37.42 detail 3 and §37.43 detail 6: the model's object for each call of a
// run, keyed by the call written and the flat name of the instance writing it,
// since every instance of a module carries the one parsed call.
using VpiCallSiteObjects =
    std::map<std::pair<const Expr*, std::string>, VpiObject*>;

// §38.36.1.1: the model's object for each statement of a run, keyed by the
// statement and the flat name of the instance it runs in.
using VpiStmtObjects =
    std::map<std::pair<const Stmt*, std::string>, VpiObject*>;

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
  // §38.36.1.1: the record of the statements made, which a cbStmt callback
  // is delivered about as each executes.
  VpiStmtObjects& stmts;
  const VpiClassDefnObjects& classes;
  const VpiSubroutineObjects& subroutines;
  // §37.25: the typespecs the compilation unit's typedefs declare, by name.
  const VpiObjectMap& unit_typespecs;
};

// What a VpiCallBuild reaches besides the run and its records: the class
// defns, the tasks and functions and the compilation unit's typespecs made.
struct VpiCallObjects {
  VpiClassDefnObjects classes;
  VpiSubroutineObjects subroutines;
  VpiObjectMap unit_typespecs;
  // Where each class defn's calls stand, and the design they were made of,
  // which a class obj made once the run is under way shapes its calls with.
  VpiClassCallSites class_sites;
  const RtlirDesign* design = nullptr;
};

// §37.42: shapes each call of `deferred` as a call a procedure's expression
// writes where it stands is shaped, once every task, function and class defn
// of `design` it may reach has its object, and any call shaping one holds in
// turn. A call no shape resolves keeps the arguments it is written with.
// Holding no call, it reads nothing of `design`, which may then be null.
void VpiShapeDeferredCalls(const RtlirDesign* design,
                           const VpiObjectMap& objects,
                           std::vector<VpiDeferredCall>& deferred,
                           const VpiCallBuild& calls,
                           const VpiAttachBuild& build);

// §11.5.1: the range written `[left:right]`, its bounds evaluated in the scope
// the attach set.
PackedRange VpiEvaluatedRange(Expr* left, Expr* right, SimContext& ctx);

// §37.11: an instance array of `kind` named `name` under `holder`, of the
// size `range` makes, reaching that range as its one range object (detail 2)
// and its bounds through vpiLeftRange and vpiRightRange.
VpiObject* VpiMakeInstanceArray(VpiObject* holder, int kind,
                                std::string_view name, const PackedRange& range,
                                const VpiAttachBuild& build);

// §37.11 with §37.5 detail 2 and §37.35 detail 4: `element` as the element of
// `array` at `index`, which it reaches through vpiIndex as a constant and
// which the array reaches it by (§38.19); it keeps its place in its scope.
void VpiAddArrayElement(VpiObject* array, VpiObject* element, int64_t index,
                        const VpiAttachBuild& build);

// §37.48 with §37.5, §37.6 and §37.9: give each instance a clocking block per
// clocking block it declares, with its clocking event and an io decl per
// clocking signal, marking the one it named default and the one it named
// global.
void AttachClockingBlocks(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build);

// §37.76 with §37.5: give each instance an alias statement per net an alias
// it writes joins to the alias's last net, with that net as its vpiRhs.
void AttachAliasStatements(const RtlirDesign* design,
                           const VpiObjectMap& objects, SimContext& ctx,
                           const VpiAttachBuild& build);

// §37.5, §37.6 and §37.9: give each instance under a default disable iff the
// condition it writes, which vpiDefaultDisableIff reaches.
void AttachDefaultDisableIffs(const RtlirDesign* design,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build);

// §37.49 and §37.50: the assertion object of the concurrent assertion an
// instance writes as an item, `assertion`, hung from `scope`, the generate
// block instance writing it or the instance itself, with its clock, its
// property spec and its actions, each built through `with`; none for a
// deferred immediate assertion, which stands as the statement its process
// runs. Answers the object made, null for none.
VpiObject* VpiMakeItemAssertion(const RtlirAssertion& assertion,
                                VpiObject* scope, SimContext& ctx,
                                const VpiStmtBuild& with);

// §37.49: give the assertion `obj` the location of its text, `range`: its
// file and the line and column it starts and ends at, and, by §37.3.6, its
// protection where that text stands inside a decryption envelope.
void VpiRecordAssertionLocation(VpiObject* obj, const SourceRange& range,
                                SimContext& ctx);

// §37.3.3: give `obj`, which stands for source text starting at `loc`, the
// file and line that text was written on, which vpiFile and vpiLineNo read,
// and, by §37.3.6, its protection where that text stands inside a decryption
// envelope; a position the parser did not record leaves all three as they
// were.
void VpiRecordWrittenLocation(VpiObject* obj, SourceLoc loc, SimContext& ctx);

// §37.11: make each instance array of modules, interfaces or programs an
// array object over its elements.
void AttachInstanceArrays(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build);

// §37.36: the udp defn object made for a UDP declaration.
using VpiUdpDefnOf = std::function<VpiObject*(const UdpDecl*)>;

// §37.35: give each instance a gate, switch or udp per primitive it
// instantiates, each with a prim term per terminal and a udp reaching the udp
// defn `udp_defn_of` gives for its UDP, and §37.11: a gate or switch array per
// instance array of them, over a primitive per element.
void AttachPrimitives(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiUdpDefnOf& udp_defn_of, SimContext& ctx,
                      const VpiAttachBuild& build);

// §37.85: make each generate block instance of each instance the gen scope it
// is, and each iteration of a loop generate an element, reached by its index,
// of the gen scope array the instance holds for the loop's block.
void AttachGenScopes(const RtlirDesign* design, const VpiObjectMap& objects,
                     const VpiAttachBuild& build);

// §37.83: make each attribute of `attrs` an attribute object, a child of
// `owner`, the object it is written on, on its definition where
// `on_definition`, with its name, value and the place it was written.
void VpiAttachAttributes(VpiObject* owner,
                         const std::vector<ResolvedAttribute>& attrs,
                         bool on_definition, SimContext& ctx,
                         const VpiAttachBuild& build);

// §37.83: the attributes elaboration resolved on the syntax node `node` of
// `mod`, the instance it stands in (RtlirModule::node_attrs); none where it
// carries none or `mod` is null, a package's or the compilation unit's.
const std::vector<ResolvedAttribute>& VpiNodeAttributes(const RtlirModule* mod,
                                                        const void* node);

// §37.83: the same, read out of `table`, a module's or the design's
// (RtlirDesign::node_attrs); none where it is null.
const std::vector<ResolvedAttribute>& VpiNodeAttributes(
    const RtlirNodeAttributes* table, const void* node);

// §37.83: the attribute objects of each port of each instance, from the
// attributes its declaration is written with. Run once the ports are made.
void AttachPortAttributes(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build);

// §37.83: the attribute objects of each instance, from its instantiation and
// its module's declaration, and of each net and variable it declares.
void AttachAttributes(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build);

// §27.4 with §37.17 and §37.28: give each variable, net and parameter a
// generate block instance declares the object the passes built for it, named
// as declared under the block's gen scope, in place of the bare one its alias
// was given. Run after every pass that resolves a name to such an object.
void AttachGenBlockStorage(const RtlirDesign* design,
                           const VpiObjectMap& objects);

// §23.6 with §37.85: move each instance a generate block instance holds from
// its module, where the run's flattened key for it put it, into the block's
// gen scope, named as written and full-named through the scope, with what it
// holds. Run after every pass that finds an object by its key.
void AttachGenBlockInstances(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiNameKeeper& keep);

// §37.14 details 3, 4 and 10: link each port of each instance to its higher
// connection, the expression the instantiation wrote for it, and its lower
// one, the instance's own net or variable of the port. The ports are those
// VpiContext::AttachDesignPorts made.
// §37.14 (figure): hang from `port` a port bit per bit of the net or variable
// it stands for inside the instance, its lowConn, in that object's order and
// each carrying its index and its place in the port's value; the bit is the
// port bit's lowConn. A port with no lowConn, or one whose lowConn has no bits,
// a scalar one among them, has none.
void VpiMakePortBits(VpiObject* port, const VpiAttachBuild& build);

void AttachPortConnections(const RtlirDesign* design,
                           const VpiObjectMap& objects, SimContext& ctx,
                           const VpiAttachBuild& build);

// §37.63: give each instance a process per procedure it declares, reaching the
// statement it runs; §37.12: an object per block its procedures write, nested
// as the blocks are, each with the variables it declares; §37.62: an event
// statement per trigger, §37.42: a call statement per task, method task and
// system task call, and an object per statement VpiBuiltStmtKind names, each
// hung from the block or statement it stands in; and §37.50: an assertion
// object per concurrent assertion written as an item (VpiMakeItemAssertion).
void AttachProcedures(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiCallBuild& calls, const VpiAttachBuild& build);

// Where an expression an instance writes outside every procedure stands: the
// design, the instance's module and the flat name its objects are keyed
// under, the generate block instances it stands in, innermost last, and the
// scope object it stands in, the instance or the gen scope of one of them.
struct VpiItemSite {
  const RtlirDesign& design;
  const RtlirModule& mod;
  const std::string& prefix;
  const std::vector<std::string_view>& gen_prefixes;
  VpiObject* scope;
};

// §37.42: what makes a call written in an expression at `site` into the tf
// call a call written in a procedure's expression there is made into, true
// where it does. Each reference it is given outlives it.
std::function<bool(const Expr& call, VpiObject* made)> VpiItemCallShaper(
    const VpiItemSite& site, const VpiObjectMap& objects,
    const VpiCallBuild& calls, const VpiAttachBuild& build);

// §8.13 with §37.31 detail 5: the class defn of the class the class defn
// `defn` extends, reached through its extends object; null for none.
VpiObject* VpiBaseClassDefn(const VpiObject* defn);

// §8.13: an object holding the variables the class defn `defn` and the classes
// it extends hold, the derived class's first, beneath `outer`, through which
// a name in a constraint of the class finds the class's properties ahead of
// the scopes around (§18.5, §18.7). It stands for nothing in the VPI model.
VpiObject* VpiClassNameScope(const VpiObject* defn, VpiObject* outer,
                             const VpiAttachBuild& build);

// Where the names in a constraint block's expressions resolve: `scope`, which
// holds the class's properties as variables, and the objects above it, then
// the instance or package whose objects `objects` keys under `prefix`, and the
// generate blocks `gen` names; with the run a constant's value is evaluated
// in.
struct VpiConstraintNames {
  const VpiObjectMap& objects;
  const std::string& prefix;
  const std::vector<std::string_view>& gen;
  VpiObject* scope;
  SimContext& ctx;
  // §37.83: the table the operators' attributes are kept in; null for none.
  const RtlirNodeAttributes* attrs = nullptr;
  // §37.42: where a call the constraint makes stands; null to leave it as made.
  const VpiCallStand* stand = nullptr;
};

// §37.34: the constraint object the constraint block `block` stands as, held
// by `holder`, a class defn, a class obj or a call of randomize, which the
// caller hangs it from: named after the block, full-named through a class
// defn holding it, automatic unless the block was declared static (detail 1,
// §18.5.10), reporting vpiExternAcc where a prototype in the class declares a
// block defined outside it (detail 3, §18.5.1), and enabled, as every
// constraint is at first (§18.9). §37.38: its items are the constraint
// expressions the block writes, in order (detail 5), each name in them
// resolved through `names`.
VpiObject* VpiMakeConstraint(const ClassMember& block, VpiObject* holder,
                             const VpiConstraintNames& names,
                             const VpiAttachBuild& build);

// §37.34 and §37.38: a distribution reaching `weighted`, the expression it
// weights, and a dist item per entry of `items`, in order, each expression an
// item writes built with `expression`: a constraint's dist and an assertion's
// (§16.14.2) alike.
VpiObject* VpiMakeDistribution(
    VpiObject* weighted, const std::vector<ConstraintDistItem>& items,
    const std::function<VpiObject*()>& alloc,
    const std::function<VpiObject*(const Expr*)>& expression);

// §37.7: give each interface instance a modport per modport its interface
// declares, each with an io decl per port it gives a direction, and §37.13:
// each io decl the vpiExpr of what the port connects to.
void AttachModports(const RtlirDesign* design, const VpiObjectMap& objects,
                    SimContext& ctx, const VpiAttachBuild& build);

}  // namespace delta
