#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_stmt.h"

namespace delta {

class Arena;
class DiagEngine;
struct ClassDecl;
struct InferenceFuncs;
struct RtlirModule;
struct RtlirParamDecl;

struct ResolvedAttribute;
enum class RtlirProcessKind : uint8_t;

struct InstantiatedCell {
  std::string_view name;
  SourceLoc loc;
};

void CollectInstantiations(const std::vector<ModuleItem*>& items,
                           std::vector<InstantiatedCell>& cells);

void CollectInstantiatedNames(const std::vector<ModuleItem*>& items,
                              std::unordered_set<std::string_view>& names);

std::vector<ResolvedAttribute> ResolveAttributes(
    const std::vector<Attribute>& attrs, DiagEngine& diag,
    const ScopeMap& scope);
std::vector<ResolvedAttribute> ResolveAttributes(
    const std::vector<Attribute>& attrs, DiagEngine& diag,
    const ScopeMap& scope, const ScopeMap& constants);
std::string_view LhsSignalName(const Expr* lhs);

uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod);

uint32_t LookupNameWidth(std::string_view name, const RtlirModule* mod);

struct FoundSignalDecl {
  const DataType* dtype = nullptr;
  uint32_t width = 0;
  bool unpacked = false;
  bool is_signed = false;
};
FoundSignalDecl FindSignalDecl(std::string_view name, const RtlirModule* mod);

PackedRange SignalDeclaredRange(std::string_view name, const RtlirModule* mod,
                                const ScopeMap& scope);
RtlirProcessKind MapAlwaysKind(AlwaysKind ak);

struct ProcessBuildEnv {
  Arena& arena;
  DiagEngine& diag;
  const InferenceFuncs* func_map = nullptr;
  const std::unordered_set<std::string_view>* const_names = nullptr;
  const std::vector<EventExpr>* global_clocking_event = nullptr;
  const std::unordered_set<std::string>* task_names = nullptr;
};
void AddProcess(RtlirProcessKind kind, ModuleItem* item, RtlirModule* mod,
                const ProcessBuildEnv& env, const ScopeMap& params);
void AddStaticAssertionProcess(RtlirProcessKind kind, ModuleItem* item,
                               RtlirModule* mod, const ProcessBuildEnv& env);

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena,
                       const ScopeMap& scope);

bool ExpandInstanceArray(
    ModuleItem* item, const RtlirModule* mod, Arena& arena,
    const ScopeMap& scope,
    const std::function<void(ModuleItem*)>& elaborate_element);

std::optional<uint32_t> InstanceArrayLength(const ModuleItem* item,
                                            const ScopeMap& scope);

bool NettypesMatch(std::string_view a, std::string_view b,
                   const std::unordered_map<std::string_view, std::string_view>&
                       nettype_canonical);

void ValidateBidirectionalSwitchConnections(
    const ModuleItem* item, const RtlirModule* mod, DiagEngine& diag,
    const std::unordered_map<std::string_view, std::string_view>&
        nettype_canonical);

bool ItemCarriesDelay(const ModuleItem* item);

void ValidateItemDelaysNonNegative(const ModuleItem* item,
                                   const ScopeMap& scope, DiagEngine& diag);

void ValidatePrimitiveOutputTerminalWidths(const ModuleItem* item,
                                           const RtlirModule* mod,
                                           const ScopeMap& scope,
                                           const ScopedDeclarations& names,
                                           DiagEngine& diag);

std::vector<size_t> PrimitiveDrivenTerminalIndices(const ModuleItem* item);

void ValidatePrimitiveDrivenTerminals(
    const ModuleItem* item, const RtlirModule* mod, const ScopeMap& scope,
    const std::vector<std::string_view>& gen_scopes, DiagEngine& diag);

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype);

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype,
                           const TypedefMap& typedefs, const ScopeMap& scope);

void RecordParamDeclRange(RtlirParamDecl& pd, const DataType& dtype,
                          const ScopeMap& scope);

int64_t ConvertOverrideValue(int64_t value, const RtlirParamDecl& pd);
std::optional<double> RealOverrideValue(const Expr* expr,
                                        const ScopeMap& scope);
int64_t RoundRealToInteger(double value);
void ApplyOverrideRealness(RtlirParamDecl& pd, std::optional<double> real);

bool ParamExpectsIntegerValue(const RtlirParamDecl& pd, const DataType& dtype);

bool TryFoldRealParamValue(RtlirParamDecl& pd, const Expr* init,
                           const DataType& dtype, const ScopeMap& scope);

void RecordStringParamValue(RtlirParamDecl& pd, const Expr* init,
                            const DataType* dtype, Arena& arena);

bool RecordStringParamChars(RtlirParamDecl& pd, const Expr* init, Arena& arena);

std::string_view ExprIdent(const Expr* e);
bool SelectPathIsConstant(const Expr* e, const ScopeMap& scope);
uint32_t SelectLhsWidth(const Expr* e, const ScopeMap& scope);
const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit);

bool HasParamPortWithoutDefault(const ModuleDecl* decl);

std::unordered_set<std::string_view> DeclaredSpecparamNames(
    const ModuleDecl* decl);

const ClassDecl* FindBaseClass(const ClassDecl* cls,
                               const CompilationUnit* unit);

std::vector<const ClassDecl*> AllClassDecls(const CompilationUnit* unit);

void AdoptReferencedType(DataType& dt, const DataType& type);

void ResolveScopeTypeRef(DataType& dt, const std::vector<ModuleItem*>& items,
                         Arena& arena);

void AdoptExpressionType(DataType& dt, const std::optional<DataType>& type,
                         Arena& arena);

bool ExprMentionsAny(const Expr* e,
                     const std::unordered_set<std::string_view>& names);

std::unordered_set<std::string_view> ClassParamNames(const ClassDecl* cls);

bool IsConstantClassParamValue(const Expr* e, const ScopeMap& scope);

std::unordered_set<std::string_view> NonIntegralParamNames(
    const std::vector<ModuleItem*>* items, const ScopeMap& values);

const DataType* FindClassScopedTypedefType(std::string_view cls_name,
                                           std::string_view type_name,
                                           const CompilationUnit* unit);

const ModuleItem* FindClassScopedTypedefItem(std::string_view cls_name,
                                             std::string_view type_name,
                                             const CompilationUnit* unit);

bool ResolveClassScopedDeclType(DataType& dtype, const TypedefMap& typedefs,
                                const CompilationUnit* unit);

struct ClassTypedefTables {
  const CompilationUnit* unit;
  TypedefMap& typedefs;
  std::unordered_map<std::string_view, std::vector<Expr*>>& td_array_dims;
  Arena& arena;
};

void RegisterClassTypedefKeys(const ClassDecl* cls, std::string_view scope,
                              const ClassTypedefTables& tables);

void ReportUnresolvedClassScopedType(const DataType& dtype, SourceLoc loc,
                                     const TypedefMap& typedefs,
                                     const CompilationUnit* unit,
                                     DiagEngine& diag);

std::string_view NestedClassKey(const DataType& dtype,
                                const CompilationUnit* unit, Arena& arena);

void ValidatePackageCycleDelays(const CompilationUnit* unit, DiagEngine& diag);

void ValidateCycleDelayCounts(const ModuleDecl* decl, const ScopeMap& scope,
                              DiagEngine& diag);

std::string_view PackageClassKey(const DataType& dtype,
                                 const TypedefMap& typedefs,
                                 const CompilationUnit* unit, Arena& arena);

bool ResolveParameterizedType(DataType& dtype, const CompilationUnit* unit,
                              DiagEngine& diag, SourceLoc loc);
bool IsRealType(DataTypeKind k);

struct VarSelectShape {
  size_t addressable_dims = 0;
  bool element_is_real = false;
  bool element_is_scalar = false;
};

RtlirNet MakeImplicitPortNet(std::string_view name, uint32_t port_width,
                             bool port_is_signed, NetType default_nettype);

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

NettypeResolutionRule ValidateNettypeResolutionFunction(
    const NettypeResolutionSig& sig);

size_t LibrarySearchPosition(std::string_view library,
                             const std::vector<std::string>& order);

bool SelectedLibraryListInForce(const std::vector<std::string>& order,
                                bool strict);

bool LibraryExcludedBySelectedList(std::string_view library,
                                   const std::vector<std::string>& order,
                                   bool strict);

inline std::pair<std::string_view, std::string_view> SplitLibCell(
    std::string_view name) {
  const std::size_t kDot = name.find('.');
  if (kDot == std::string_view::npos) return {{}, name};
  return {name.substr(0, kDot), name.substr(kDot + 1)};
}

bool IsLiteralKind(ExprKind k);

std::string HierInstancePath(std::string_view parent, const HierPath& gen_steps,
                             std::string_view inst_name);

UdpDecl* FindUdpInLibrary(std::string_view library, std::string_view cell,
                          CompilationUnit* unit);

bool CellUseOverrideApplies(std::string_view src_lib, std::string_view name,
                            CompilationUnit* unit);

std::unordered_set<std::string_view> NonConfigCellNames(
    const CompilationUnit* unit);

bool UseClauseNamesConfig(const ConfigRule* rule, const ConfigDecl* cfg,
                          const CompilationUnit* unit);

}  // namespace delta
