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

namespace delta {

class Arena;
class SimContext;
struct ClassDecl;
struct DataType;
struct EventExpr;
enum class DataTypeKind : uint8_t;
struct Expr;
struct ModuleItem;
struct PropertyExprNode;
struct SeqLinearBody;
struct RtlirAssertion;
struct RtlirPropertyDecl;
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
  // §27.4: the prefixes of the generate block instances the site stands in,
  // innermost last, whose declarations a name finds ahead of the instance's;
  // null where it stands in none.
  const std::vector<std::string_view>* gen_prefixes = nullptr;
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

// Where the names of an expression written in an instance resolve: the
// instance, whose objects `objects` keys under `prefix`, and the generate
// block instances it stands in, by their prefixes, innermost last, whose
// declarations a name finds first (§27.4).
struct VpiExprNames {
  const VpiObjectMap& objects;
  const std::string& prefix;
  const std::vector<std::string_view>& gen_prefixes;
};

// The same of an expression written in the generate block instances `names`
// carries.
VpiObject* VpiGenBlockExpression(const Expr* expr, const VpiExprNames& names,
                                 SimContext& ctx, const VpiAttachBuild& build);

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

// The kind of value a built-in method is called on: a string (§6.16), an enum
// (§6.19.5), a fixed-size, dynamic or associative array or a queue (§7.4,
// §7.5, §7.8, §7.10), or none of them.
enum class VpiBuiltInHolder : uint8_t {
  kNone,
  kString,
  kEnum,
  kFixedArray,
  kDynamicArray,
  kAssocArray,
  kQueue,
};

// Whether `method` is one of the built-in methods of a value of `holder`'s
// kind: §6.16's of a string, §6.19.5's of an enum, §7.5's of a dynamic array,
// §7.9's of an associative array, §7.10.2's of a queue, and §7.12's of any
// unpacked array but §7.12.2's ordering methods for an associative one.
bool VpiIsBuiltInMethod(VpiBuiltInHolder holder, std::string_view method);

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
// wait, a disable or disable fork (§37.77), or an assertion: an immediate
// one, or a concurrent one embedded in procedural code (§37.50), or an expect
// statement (§37.73); 0 for a statement of another kind.
int VpiBuiltStmtKind(const Stmt& stmt);

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
// under first_match where written, each built through `with`; null for a body
// holding an operand clocked on its own or match items inside a first_match.
VpiObject* VpiSequenceExprObject(const SeqLinearBody& body,
                                 const VpiStmtBuild& with);

// §37.52: the property expr the property tree `node` stands for: the
// expression of a Boolean, or the operation of a property operator (detail
// 2) over its operands, each built through `with`; null for a form not built.
VpiObject* VpiPropertyExprObject(const PropertyExprNode* node,
                                 const VpiStmtBuild& with);

// §37.52: the property spec of `parts`, hung from `holder`.
VpiObject* VpiMakePropertySpecOf(VpiObject* holder,
                                 const VpiPropertySpecParts& parts,
                                 const VpiStmtBuild& with);

// §37.51: the property inst the spec `instance` writes, an instance of a
// declared property, hung from the assertion `holder`, reaching the property
// decl of that name the scope around `holder` declares and its arguments, each
// built through `with`.
VpiObject* VpiMakePropertyInst(VpiObject* holder, const Expr& instance,
                               const VpiStmtBuild& with);

// §37.22: a range object under `parent` of the dimension `bounds`, an empty
// range where it has none.
VpiObject* VpiRangeObject(VpiObject* parent,
                          const std::optional<PackedRange>& bounds,
                          const VpiAttachBuild& build);

// Where a property decl is built: `scope`, the instance or the generate block
// instance declaring it; the typespecs of the compilation unit's typedefs,
// which a formal's type may name; and the run its packed dimensions are
// evaluated in.
struct VpiPropertyDeclSite {
  VpiObject* scope;
  const VpiObjectMap& unit_typespecs;
  SimContext& ctx;
};

// §37.12 and §37.51: the property decl of the property `declared` stands
// for, hung from the scope declaring it, `at.scope` or the clocking block it
// holds that declares it, with its formals, their typespecs, its variables
// and its property spec, each built through `with`; null where that clocking
// block has no object.
VpiObject* VpiMakePropertyDecl(const RtlirPropertyDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with);

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
  // §37.25: the typespecs the compilation unit's typedefs declare, by name.
  const VpiObjectMap& unit_typespecs;
};

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

// §37.49 and §37.50: the assertion object of the concurrent assertion an
// instance writes as an item, `assertion`, hung from `scope`, the generate
// block instance writing it or the instance itself, with its clock, its
// property spec and its actions, each built through `with`; none for a
// deferred immediate assertion, which stands as the statement its process
// runs.
void VpiMakeItemAssertion(const RtlirAssertion& assertion, VpiObject* scope,
                          SimContext& ctx, const VpiStmtBuild& with);

// §37.49: give the assertion `obj` the location of its text, `range`: its
// file and the line and column it starts and ends at.
void VpiRecordAssertionLocation(VpiObject* obj, const SourceRange& range,
                                SimContext& ctx);

// §37.11: make each instance array of modules, interfaces or programs an
// array object over its elements.
void AttachInstanceArrays(const RtlirDesign* design,
                          const VpiObjectMap& objects,
                          const VpiAttachBuild& build);

// §37.35: give each instance a gate or switch per primitive it instantiates,
// each with a prim term per terminal, and §37.11: a gate or switch array per
// instance array of them, over a primitive per element.
void AttachPrimitives(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build);

// §37.85: make each generate block instance of each instance the gen scope it
// is, and each iteration of a loop generate an element, reached by its index,
// of the gen scope array the instance holds for the loop's block.
void AttachGenScopes(const RtlirDesign* design, const VpiObjectMap& objects,
                     const VpiAttachBuild& build);

// §27.4 with §37.17: give each variable and net a generate block instance
// declares the object the passes built for it, named as declared under the
// block's gen scope, in place of the bare one its alias was given. Run after
// every pass that resolves a name to such an object.
void AttachGenBlockStorage(const RtlirDesign* design,
                           const VpiObjectMap& objects);

// §37.14 details 3, 4 and 10: link each port of each instance to its higher
// connection, the expression the instantiation wrote for it, and its lower
// one, the instance's own net or variable of the port. The ports are those
// VpiContext::AttachDesignPorts made.
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

// §37.7: give each interface instance a modport per modport its interface
// declares, each with an io decl per port it gives a direction, and §37.13:
// each io decl the vpiExpr of what the port connects to.
void AttachModports(const RtlirDesign* design, const VpiObjectMap& objects,
                    SimContext& ctx, const VpiAttachBuild& build);

}  // namespace delta
