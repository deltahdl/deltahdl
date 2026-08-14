#pragma once

#include <cstddef>
#include <cstdint>
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
};
void AddProcess(RtlirProcessKind kind, ModuleItem* item, RtlirModule* mod,
                const ProcessBuildEnv& env);

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena);

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

std::string_view ExprIdent(const Expr* e);
const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit);

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
bool IsRealType(DataTypeKind k);

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
  bool argument_is_dynamic_array_of_type = false;
  bool is_automatic = false;
  bool is_class_method = false;
  bool is_static_method = false;
};

// Returns true iff the resolution-function signature conforms to §6.6.7.
bool ValidateNettypeResolutionFunction(const NettypeResolutionSig& sig);

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
