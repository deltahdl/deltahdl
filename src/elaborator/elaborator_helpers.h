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
                                           DiagEngine& diag);

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype);

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype,
                           const TypedefMap& typedefs, const ScopeMap& scope);

int64_t ConvertOverrideValue(int64_t value, const RtlirParamDecl& pd);

bool ParamExpectsIntegerValue(const RtlirParamDecl& pd, const DataType& dtype);

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

}  // namespace delta
