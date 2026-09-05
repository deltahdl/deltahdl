#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

class Arena;
class DiagEngine;
struct RtlirModule;
struct RtlirParamDecl;

struct ResolvedAttribute;
enum class RtlirProcessKind : uint8_t;

// What one instantiation asks for: the name of the cell it instantiates, and
// where that name is written. A report about a cell no declaration answers to
// stands at that position, so somebody whose design named a cell that is not
// there is told which instantiation asked for it.
struct InstantiatedCell {
  std::string_view name;
  SourceLoc loc;
};

// §23.3.1: appends to `cells` every instantiation in `items`, descending
// through generate constructs -- whose alternatives are reached only by
// looking inside them -- and through nested module declarations. A name two
// instantiations write is appended twice, each with its own position, so a
// caller that wants each name once says which of them it keeps.
void CollectInstantiations(const std::vector<ModuleItem*>& items,
                           std::vector<InstantiatedCell>& cells);

// The same walk as CollectInstantiations, reduced to the set of names it
// reaches. Names already present stay, so a walk over the item lists of
// several declarations accumulates into one set. Which declaration each name
// belongs to, and whether any declaration answers to it at all, is the
// caller's question: deciding which modules no instance names (the tops of a
// compilation unit) and deciding whether every name reached has a declaration
// behind it are both asked of the same set.
void CollectInstantiatedNames(const std::vector<ModuleItem*>& items,
                              std::unordered_set<std::string_view>& names);

std::vector<ResolvedAttribute> ResolveAttributes(
    const std::vector<Attribute>& attrs, DiagEngine& diag,
    const ScopeMap& scope = {});
// §10.3.2: the name a left-hand side drives as a whole, empty where it drives
// no single declared signal under a name. The clause admits a concatenation, a
// select and a member access there as well as a plain name, none of which names
// one signal, and a malformed left-hand side is absent altogether.
std::string_view LhsSignalName(const Expr* lhs);

uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod);

// The range a select on the signal named `name` in `mod` resolves its indices
// against: the outermost packed dimension of that signal's declaration, folded
// in `scope`. Falls back to [width-1:0] -- where an index and a bit offset
// coincide -- in every case the simulator addresses the storage that way too:
//
//   - `name` names no variable, net or port of `mod`. A port answers from
//     RtlirPort::dtype, which carries the packed dimension its header declared;
//     the lowering records no packed range for port storage.
//   - the declaration carries no packed dimension (an `int`, a scalar, a
//     string), or a bound that does not fold in this scope.
//   - a further packed dimension makes the outermost range index elements
//     rather than bits (§7.4.1), which is the fallback
//     Variable::BitSelectRange makes for a select addressed by bit.
//   - the folded bounds do not span the signal's width, so a range read off
//     them would misaddress every bit -- as RecordPackedRange requires.
//   - a bound is negative. A synthesized index is an unsigned integer literal,
//     so a negative index is not expressible here.
PackedRange SignalDeclaredRange(std::string_view name, const RtlirModule* mod,
                                const ScopeMap& scope);
RtlirProcessKind MapAlwaysKind(AlwaysKind ak);

// §9.2: the elaboration environment in which a procedural process is built and
// added to a module -- the arena it is allocated from, the diagnostics sink for
// its legality checks, and an optional map of subroutine declarations consulted
// when expanding the process's sensitivity list.
struct ProcessBuildEnv {
  Arena& arena;
  DiagEngine& diag;
  const std::unordered_map<std::string_view, const ModuleItem*>* func_map =
      nullptr;
  // §9.2.2.2.1: names that are elaboration-time constants (parameters,
  // localparams, specparams) so the inferred sensitivity list can drop them --
  // only nets and variables belong in the list.
  const std::unordered_set<std::string_view>* const_names = nullptr;
  // §14.14 rule a): the event expression of the global clocking declaration in
  // the enclosing module, interface, checker, or program instance scope, which
  // an event control naming $global_clock in the process body is rewritten
  // into. Null where that scope declares no global clocking, in which case the
  // body is used as it stands and §14.14's own report of a $global_clock
  // reference with no declaration in scope is the only account of it.
  const std::vector<EventExpr>* global_clocking_event = nullptr;
};
void AddProcess(RtlirProcessKind kind, ModuleItem* item, RtlirModule* mod,
                const ProcessBuildEnv& env);

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena);

// §28.3.6: expands an instance array written with a range into one instance per
// array element, calling `elaborate_element` once for each with `item` holding
// that element's own terminal list -- a terminal as wide as the array replaced
// by its [p] bit-select, so the LSB reaches the element at the right-hand index
// of the range, and a single-bit terminal left as it stands so every element
// sees it. The whole terminal list is restored before returning, so `item` is
// left as the caller passed it.
//
// The array length is taken from the widest terminal rather than from the
// range bounds. The two are the same number for a source that satisfies
// §28.3.6, and CheckGateInstanceArrayTerminalWidths
// (src/elaborator/elaborator_items.cpp) has already reported a terminal that is
// neither scalar nor array-length by the time this is called.
//
// Returns false, having called `elaborate_element` no times, when every
// terminal is single-bit: there is then nothing to distribute, and the caller
// elaborates `item` as the one instance it already is.
//
// Shared because §29.8 makes this one rule for two kinds of instance -- an
// array of user-defined primitive instances connects its terminals by "the
// terminal connection rules ... outlined in 28.3.6", the rules an array of
// gates connects by.
bool ExpandInstanceArray(
    ModuleItem* item, const RtlirModule* mod, Arena& arena,
    const std::function<void(ModuleItem*)>& elaborate_element);

// §6.7.1: "Certain restrictions apply to the data type of a net. A valid data
// type for a net shall be one of the following: a) A 4-state integral type ...
// b) A fixed-size unpacked array or unpacked structure or union, where each
// element has a valid data type for a net." Reports `dtype` at `loc` when it is
// not one of those. Shared because a net is not only what a net declaration
// produces: §23.2.2.3 makes a port with the port kind omitted a net too, and
// the rule that decides what such a thing may carry is one rule wherever the
// net came from.
void ValidateNetDataTypeIs4State(const DataType& dtype,
                                 const TypedefMap& typedefs, DiagEngine& diag,
                                 SourceLoc loc);

// §6.22.6: a nettype matches itself and the nettype of nets declared using it,
// and a renaming alias of a user-defined nettype matches the nettype it
// renames. Two nettype names match when they resolve to the same canonical
// (source) nettype; `nettype_canonical` maps each nettype name to its canonical
// name.
bool NettypesMatch(std::string_view a, std::string_view b,
                   const std::unordered_map<std::string_view, std::string_view>&
                       nettype_canonical);

void ValidateBidirectionalSwitchConnections(
    const ModuleItem* item, const RtlirModule* mod, DiagEngine& diag,
    const std::unordered_map<std::string_view, std::string_view>&
        nettype_canonical);

void ValidatePrimitiveOutputTerminalWidths(const ModuleItem* item,
                                           const RtlirModule* mod,
                                           const ScopeMap& scope,
                                           DiagEngine& diag);

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype);

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype,
                           const TypedefMap& typedefs, const ScopeMap& scope);

// §11.5.1: records on `pd` the two bounds of the packed range its declaration
// was written with, folded in `scope`. The declared width does not answer which
// bit an index reaches -- the clause sets `logic [15:0] acc` beside
// `logic [2:17] acc` and observes that one value of an index addresses a
// different bit in each -- so a select on the parameter needs the bounds
// themselves. Leaves `pd` untouched, and its has_decl_range_bounds flag clear,
// when the declaration carries no packed range or a bound that does not fold
// here; the parameter is then addressed as [width-1:0], where an index and a
// bit offset are the same number.
void RecordParamDeclRange(RtlirParamDecl& pd, const DataType& dtype,
                          const ScopeMap& scope);

int64_t ConvertOverrideValue(int64_t value, const RtlirParamDecl& pd);

bool ParamExpectsIntegerValue(const RtlirParamDecl& pd, const DataType& dtype);

// §6.20.2: a parameter declared with a real type takes a real value. Folding it
// as an integer either loses the fraction or fails outright, and a failure
// leaves the parameter unresolved -- which is not a value at all, so nothing is
// lowered for it and a reference finds no such name at run time. Keeps the
// double on `pd` and marks it, so the lowering can reproduce it as the real it
// is. Returns false, leaving `pd` untouched, when `dtype` is not a real type or
// `init` does not fold to a real constant; a parameter declared in either of
// the two syntactic positions -- a parameter port or a module item -- is
// resolved through this before the integer folds are tried.
bool TryFoldRealParamValue(RtlirParamDecl& pd, const Expr* init,
                           const DataType& dtype, const ScopeMap& scope);

// §6.16: records on `pd` the characters of a string parameter's value, so that
// a later fold can read the length §6.16.1's `len()` returns. Leaves
// resolved_value alone, which the §11.10 packed fold has already written and
// which the rest of the elaborator reads. The characters are copied into
// `arena` because resolved_string is a std::string_view. Leaves `pd`
// untouched, and its is_string_value flag clear, when `dtype` is not `string`
// -- §5.13 associates `len()` with `string` alone -- or `init` does not fold to
// a constant string.
void RecordStringParamValue(RtlirParamDecl& pd, const Expr* init,
                            const DataType* dtype, Arena& arena);

// The same recording without the check on the declared type, for a caller that
// already knows the parameter holds a string value and is replacing the
// characters rather than establishing them. Returns false, leaving `pd`
// untouched, when `init` does not fold to a constant string -- which tells such
// a caller that the characters it meant to replace are still the old ones.
bool RecordStringParamChars(RtlirParamDecl& pd, const Expr* init, Arena& arena);

std::string_view ExprIdent(const Expr* e);
const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit);

// Whether any identifier or callee anywhere in `e` is one of `names`. A caller
// that has failed to fold an expression asks this to tell a value it cannot
// compute yet from one it can never compute.
bool ExprMentionsAny(const Expr* e,
                     const std::unordered_set<std::string_view>& names);

// Every parameter name `cls` declares: its type parameters, its #() parameter
// ports and its body parameter declarations. §6.20.1 gives such a name no value
// until the class is specialized, so an expression mentioning one is not a
// constant expression that failed to fold.
std::unordered_set<std::string_view> ClassParamNames(const ClassDecl* cls);

// §8.23: the type that the class-scoped name `cls_name::type_name` denotes,
// where `cls_name` names a class and `type_name` names a typedef declared in
// its body. Returns null when no such class is visible or the class declares no
// such typedef. §8.23 names the type operator as one of the contexts a class
// scope resolution may appear in, so both forms of that operator -- the data
// type `type(C::T)` and the expression form of a type parameter default --
// resolve their prefix through this. Defined in
// elaborator_validate_struct_types.cpp.
const DataType* FindClassScopedTypedefType(std::string_view cls_name,
                                           std::string_view type_name,
                                           const CompilationUnit* unit);

// §8.23: rewrites `dtype` in place when it is a type name carrying a class
// scope prefix -- the `Cfg::my_type` of `Cfg::my_type x;` -- and that prefix
// names a visible class declaring that typedef. Returns false, leaving `dtype`
// untouched, wherever that does not hold. Defined in
// elaborator_validate_struct_types.cpp.
//
// `typedefs` is asked first and left in charge wherever it answers, because
// "scope_name::type_name" is also the key a package typedef and a
// compilation-unit class typedef are recorded under, and the class walk cannot
// tell a package from a class of the same name. What this adds is the case that
// key never covers: RegisterClassTypedefs fills the map from
// CompilationUnit::classes, which the parser fills from a top-of-file class
// alone, so a class written inside a module contributes no key at all.
// FindClassDecl reaches one, which is why `type(Cfg::my_type)` resolves against
// a module-local class while the bare declaration beside it sized itself at
// zero bits and unsigned.
//
// Registering module-local classes into the map instead would be the other way
// round, and TypedefMap is one flat map for the whole compilation unit: two
// modules each declaring a `class Cfg` would write one "Cfg::my_type" key and
// silently take each other's type. FindClassDecl answers null on that ambiguity
// through TakeUniqueMatch.
//
// DataType::scope_name is left as written rather than cleared, so a prefix that
// a later pass judges under §8.23's restriction on which contexts may carry one
// still has the prefix to judge.
bool ResolveClassScopedDeclType(DataType& dtype, const TypedefMap& typedefs,
                                const CompilationUnit* unit);

// §6.18: rewrites `dtype` in place to the type a typedef name stands for, so a
// return type written as a user-defined name carries the width and signedness
// that name was declared with. Returns false, leaving `dtype` untouched,
// wherever the name resolves to nothing this can carry. Defined in
// elaborator_validate_struct_types.cpp.
//
// The simulator has no typedef table: EvalTypeWidth(const DataType&) answers 0
// for a kNamed type and every caller under src/simulator/ turns a 0 into 32, so
// a function or a randsequence production declared to return `nib` returned 32
// bits whatever `nib` was. The table is the elaborator's, so the name is
// resolved here and the simulator goes on reading a number.
//
// It is used for a return type rather than for every named type, because a
// variable's declared type is already resolved where the width is computed --
// ElaborateVarDecl calls the resolving EvalTypeWidth overload with the table --
// and a return type is what nothing did that for.
bool ResolveNamedReturnType(DataType& dtype, const TypedefMap& typedefs);

// §8.23: "When a type name is used, the name shall resolve to a type after
// elaboration." Reports a declared type whose class scope prefix names a
// visible class that declares nothing under that name, which otherwise sizes
// the declared object at zero bits and says nothing at all. `loc` is where the
// declaration stands. Defined in elaborator_validate_struct_types.cpp.
//
// Only that one shape is reported, and the guards are what keep the report off
// the other prefixes the same clause admits: the left operand may be "a class
// type name, package name (see 26.2), covergroup type name, coverpoint name,
// cross name (see 19.5, 19.6), typedef name, or type parameter name", and
// FindClassDecl answering a class is what separates the first from the rest. A
// prefix this tool resolves by no route stays as silent as it was rather than
// becoming a report about a legal declaration. A class that extends another is
// left alone for the same reason, since the members walked are the class's own
// and not the ones it inherits, and a prefix carrying specialization arguments
// is ResolveParameterizedType's to resolve.
void ReportUnresolvedClassScopedType(const DataType& dtype, SourceLoc loc,
                                     const TypedefMap& typedefs,
                                     const CompilationUnit* unit,
                                     DiagEngine& diag);

// §8.25: rewrites `dtype` in place when it names a member of a specialization
// of a parameterized class, substituting the arguments DataType::type_params
// carries for the class's own parameters. Returns false, leaving `dtype`
// untouched, when it carries no arguments, when its scope_name reaches no
// visible class, or when the member it names does not alias one of the
// substituted parameters. Both the declared form `C#(int)::T v;` and the
// override form `child #(.P(C#(int)::T)) u();` resolve through this, so a
// caller outside Elaborator passes the compilation unit rather than reading it
// off a member. `loc` is where the specialization was written, and is the
// position of the §23.10.2.2 reports the arguments earn: a named argument
// carrying a name the class does not declare, and one assigning a name a second
// argument already assigned. Defined in elaborator_validate_struct_types.cpp.
bool ResolveParameterizedType(DataType& dtype, const CompilationUnit* unit,
                              DiagEngine& diag, SourceLoc loc);
bool IsRealType(DataTypeKind k);

// §11.5.2 fixes how many addresses a select may carry before §11.5.1 judges it:
// "To express bit-selects or part-selects of array elements, the desired word
// shall first be selected by supplying an address for each dimension. Once
// selected, bit-selects and part-selects shall be addressed in the same manner
// as net and variable bit-selects and part-selects (see 11.5.1)." So a select
// chain written on a declaration is measured against the dimensions that
// declaration has, and the address after the last of them is the one §11.5.1
// rules on.
//
// `addressable_dims` counts the unpacked dimensions and the vector dimensions
// together, because an address spends one of either. A packed dimension
// contributes one, and an integer atom type or a packed aggregate contributes
// one for the implicit vector it presents. The two flags say which alternative
// of §11.5.1's sentence -- "A bit-select or part-select of a scalar, or of a
// real variable or real parameter, shall be illegal" -- the operand at that
// depth falls under, and a declaration whose operand falls under neither gets
// no entry.
struct VarSelectShape {
  size_t addressable_dims = 0;
  bool element_is_real = false;
  bool element_is_scalar = false;
};

// Constructs the implicit net that an identifier acquires when it is used as a
// port expression. This is the single point shared by two subclauses: §6.10
// fixes the net's kind and size -- the default net type, sized to the vector
// width of the port expression declaration -- while §23.2.2.1 fixes its
// signedness -- such a net is unsigned unless the port itself is declared
// signed. Both subclauses depend on the same materialization, so they share it.
RtlirNet MakeImplicitPortNet(std::string_view name, uint32_t port_width,
                             bool port_is_signed, NetType default_nettype);

// §6.6.7: the structural constraints a user-defined resolution function for a
// nettype whose data type is T must satisfy. The function shall return T, take
// a single input argument that is a dynamic array of T, and be automatic (hold
// no state). A class method used as a resolution function shall be a static
// method, since it is called in a context where no class object is involved.
struct NettypeResolutionSig {
  bool return_type_matches_nettype = false;
  bool single_input_argument = false;
  bool argument_is_input = false;
  bool argument_is_dynamic_array = false;
  bool argument_element_type_matches = false;
  bool is_automatic = false;
  bool is_class_method = false;
  bool is_static_method = false;
};

// The §6.6.7 requirement a resolution-function signature breaks, one value per
// requirement the clause states, so a report can name the one that failed.
// kConforming is the signature that breaks none of them.
enum class NettypeResolutionRule : uint8_t {
  kConforming,
  kReturnType,
  kArgumentCount,
  kArgumentDirection,
  kArgumentIsDynamicArray,
  kArgumentElementType,
  kAutomaticLifetime,
  kClassStaticMethod,
};

// Returns the first §6.6.7 requirement `sig` breaks, or kConforming.
NettypeResolutionRule ValidateNettypeResolutionFunction(
    const NettypeResolutionSig& sig);

// §33.6.1: how far into a library search order `library` sits. Absent a
// configuration the order is the one the library map declared its libraries in,
// and a name reaches the cell held by the first library searched that holds
// one, so a smaller position is reached first. A library the order does not
// name is searched after every library it does.
size_t LibrarySearchPosition(std::string_view library,
                             const std::vector<std::string>& order);

// §33.4.1.5, §33.6.2: whether a library list a configuration selected is in
// force over `order`. A default clause names the libraries to search and so
// replaces the order the library map established with the one it names, which
// `strict` records. A list naming no library selects nothing, and selecting
// nothing is what having selected no list already means, so an empty order is
// not a list in force.
bool SelectedLibraryListInForce(const std::vector<std::string>& order,
                                bool strict);

// §33.6.2: whether a library list in force over `order` leaves `library` out.
// A library the selected list does not name is not searched, so a description
// held only by such a library is not used at all -- it is not merely ranked
// behind the listed ones. Answers false wherever no list is in force, since
// then no library is left out.
bool LibraryExcludedBySelectedList(std::string_view library,
                                   const std::vector<std::string>& order,
                                   bool strict);

// §33.6.4: the library list an instance selection clause put in force over the
// instance at `inst_path`, or nullptr when no clause in `overrides` covers it.
// Each entry pairs the path a clause named with the list it named there. Such a
// list governs the instance the clause names and is inherited by every
// descendant of that instance, so a path is covered both by a clause naming it
// outright and by a clause naming any of its ancestors. Inheritance runs down
// the hierarchy rather than across the spelling of a name, so a clause path
// counts as an ancestor only when the whole of it is matched and the next
// character of the covered path opens a further level: `top.a` names no
// ancestor of `top.a1`. Where two clauses cover one path, the longer -- the one
// naming the nearer ancestor -- is the one that governs. The returned list is
// owned by `overrides`.
const std::vector<std::string>* InstanceLiblistForPath(
    const std::string& inst_path,
    const std::vector<std::pair<std::string, std::vector<std::string>>>&
        overrides);

// §33.2.1: the primitive named `cell` that `library` holds, or nullptr when it
// holds no such primitive. A primitive is one of the kinds of design element a
// library holds a cell of, and it is the one kind a search over modules,
// interfaces, programs and checkers does not reach, so a name bound outright to
// a library's cell is looked for here as well as there.
UdpDecl* FindUdpInLibrary(std::string_view library, std::string_view cell,
                          CompilationUnit* unit);

// §33.4.1.4: whether a cell selection clause qualified by `src_lib` reaches
// the cell named `name`. Qualifying the selection with a library confines it
// to the cell that library itself defines, so the clause selects nothing when
// the named library defines no cell of the name -- of any kind a library holds
// a cell of, a primitive included. An unqualified clause, which leaves
// `src_lib` empty, selects the name wherever it appears.
bool CellUseOverrideApplies(std::string_view src_lib, std::string_view name,
                            CompilationUnit* unit);

// §33.2.1: the names under which the compilation unit's libraries hold cells
// that are not configurations. A library is a collection of cells, a cell is a
// design element, and a cell carries the name of the design element it was
// made from -- so a module, a primitive, an interface, a program and a checker
// each contribute their own declared name. A configuration is a design element
// too, and is left out here on purpose: this set answers whether a name reaches
// a cell other than a configuration, which is what decides whether naming the
// configuration takes the ':config' extension.
std::unordered_set<std::string_view> NonConfigCellNames(
    const CompilationUnit* unit);

// §33.2.1: whether the use clause of `rule` names a configuration rather than
// an ordinary cell. The ':config' extension names one explicitly, and it shall
// be written wherever a configuration shares its name with a module or a
// primitive, because the plain name reaches the module or primitive there. A
// name carried by no other design element is unambiguous on its own, so the
// extension is optional and the plain name still reaches the configuration.
// `cfg` is the configuration the rule was written in; a configuration does not
// name itself.
bool UseClauseNamesConfig(const ConfigRule* rule, const ConfigDecl* cfg,
                          const CompilationUnit* unit);

}  // namespace delta
