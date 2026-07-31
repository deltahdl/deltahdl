#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

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

std::vector<ResolvedAttribute> ResolveAttributes(
    const std::vector<Attribute>& attrs, DiagEngine& diag,
    const ScopeMap& scope = {});
uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod);

// The range a select on the signal named `name` in `mod` resolves its indices
// against: the outermost packed dimension of that signal's declaration, folded
// in `scope`. Falls back to [width-1:0] -- where an index and a bit offset
// coincide -- in every case the simulator addresses the storage that way too:
//
//   - `name` is not a variable or net of `mod`. A port is one such case, since
//     RtlirPort carries no data type and the lowering records no packed range
//     for port storage either.
//   - the declaration carries no packed dimension (an `int`, a scalar, a
//     string), or a bound that does not fold in this scope.
//   - a further packed dimension makes the outermost range index elements
//     rather than bits (§7.4.1), which is the fallback
//     Variable::BitSelectRange makes for a select addressed by bit.
//   - the folded bounds do not span the signal's width, so a range read off
//     them would misaddress every bit -- as RecordPackedRange requires.
//   - a bound is negative. A synthesized index is an unsigned integer literal,
//     so a negative index is not expressible here.
DeclaredPackedRange SignalDeclaredRange(std::string_view name,
                                        const RtlirModule* mod,
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
