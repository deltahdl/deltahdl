#ifndef DELTA_SIMULATOR_LOWERER_REGISTER_H_
#define DELTA_SIMULATOR_LOWERER_REGISTER_H_

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/sim_context_types.h"

namespace delta {

class Arena;
struct AssocArrayObject;
struct ClassDecl;
struct ClassTypeInfo;
struct DataType;
struct Expr;
struct ModuleItem;
struct Net;
struct PackageDecl;
struct QueueObject;
struct RtlirDesign;
struct RtlirModule;
struct RtlirPort;
class SimContext;
struct Variable;

bool PortDefaultsToZero(const RtlirPort& port);

uint64_t NetDecayTicks(const RtlirNet& net, const TimeScale& scale,
                       TimeUnit precision);

void RecordPackedRange(const DataType* dt, Variable* v, SimContext& ctx,
                       Arena& arena);

void RegisterAggregateLayout(std::string_view name, const DataType* dtype,
                             uint32_t width, SimContext& ctx, Arena& arena);

const StructTypeInfo* InlineAggregateLayout(const DataType& written,
                                            SimContext& ctx);

bool HasFourStateMember(const StructTypeInfo& info);

void MarkUnpackedStructStorage(std::string_view name, Variable* v,
                               bool fill_defaults, SimContext& ctx);

void CreateArrayElements(std::string_view name, const RtlirVariable& var,
                         SimContext& ctx, Arena& arena);
void InitArrayElements(std::string_view name, const RtlirVariable& var,
                       SimContext& ctx, Arena& arena);
void InitQueueFromDeclInit(QueueObject* q, const Expr* init, SimContext& ctx,
                           Arena& arena);
void InitAssocFromDeclInit(const Expr* init, AssocArrayObject* aa,
                           SimContext& ctx, Arena& arena);

void CreatePortVariable(std::string_view name, const RtlirPort& port,
                        SimContext& ctx, Arena& arena);

void RegisterDesignTypeLayouts(const RtlirDesign* design, SimContext& ctx,
                               Arena& arena);

void RegisterTypeLayout(std::string_view name, const DataType* dtype,
                        SimContext& ctx, Arena& arena);
EnumMemberInfo EnumMemberInfoOf(const RtlirEnumMember& m, uint32_t width,
                                SimContext& ctx, Arena& arena);

void RegisterDesignEnumTypes(const RtlirDesign* design, SimContext& ctx,
                             Arena& arena);
void RegisterPackageClassVariables(const RtlirDesign* design, SimContext& ctx,
                                   Arena& arena);
void RegisterUnitClassVariables(const RtlirDesign* design, SimContext& ctx,
                                Arena& arena);
std::string UnitBuiltinClassKey(const DataType& type);

const DataType* ParamValueType(const RtlirParamDecl& param);

void ReevaluateParamValue(const RtlirParamDecl& param, Variable* var,
                          SimContext& ctx, Arena& arena);

bool UnfoldedParamEvaluable(const RtlirParamDecl& param, SimContext& ctx);

Net* CreateNetStorage(std::string_view name, const RtlirNet& net,
                      const TimeScale& scale, SimContext& ctx, Arena& arena);

void CreateNetArrayElements(std::string_view name, const RtlirNet& net,
                            const TimeScale& scale, SimContext& ctx,
                            Arena& arena);

void CreateDeclaredNet(std::string_view name, const RtlirNet& net,
                       const TimeScale& scale, SimContext& ctx, Arena& arena);
void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void CreatePortStorage(const std::string& prefix, const RtlirPort& port,
                       SimContext& ctx, Arena& arena);
void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx);
void RegisterModuleLets(const RtlirModule* mod, std::string_view prefix,
                        SimContext& ctx);
void RegisterInstanceSubroutines(const RtlirModule* mod,
                                 const std::string& inst_prefix,
                                 SimContext& ctx, Arena& arena);
void RegisterGenBlockSubroutines(const RtlirModule* mod,
                                 const std::string& key_prefix,
                                 const std::string& inst_prefix,
                                 SimContext& ctx, Arena& arena);
std::string GenBlockName(const HierPath& path);

const ModuleItem* WithPackageOwnType(const ModuleItem* item,
                                     std::string_view pkg,
                                     const SimContext& ctx, Arena& arena);

void RecordPackageVcdKind(const ModuleItem* item, const Variable& var,
                          std::string_view qname, SimContext& ctx);

void RegisterModuleDpiImports(const RtlirModule* mod, SimContext& ctx);
void RegisterDesignScopeDpiImports(const RtlirDesign* design, SimContext& ctx);
void RegisterPackageScopedSubroutines(const RtlirDesign* design,
                                      SimContext& ctx, Arena& arena);
void CreatePackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                                Arena& arena);
void CreateUnitDataVariables(const RtlirDesign* design, SimContext& ctx,
                             Arena& arena);
void CreateUnitNets(const RtlirDesign* design, SimContext& ctx, Arena& arena);
void AliasUnitDataItems(const RtlirDesign* design, const RtlirModule* mod,
                        std::string_view inst_prefix, SimContext& ctx,
                        Arena& arena);
void AliasVariableKinds(std::string_view key, std::string_view qname,
                        SimContext& ctx, Arena& arena);
bool ModuleDeclaresName(const RtlirModule* mod, std::string_view name);
void InitPackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena);
void InitUnitDataVariables(const RtlirDesign* design, SimContext& ctx,
                           Arena& arena);
void ConstructDataClassInitializers(const RtlirDesign* design, SimContext& ctx,
                                    Arena& arena);
void AliasPackageExports(const RtlirDesign* design, SimContext& ctx,
                         Arena& arena);
std::optional<int64_t> FoldPackageParamValue(const ModuleItem& item,
                                             const PackageDecl& pkg,
                                             const ScopeMap& values,
                                             const SimContext& ctx);
void RegisterPackageEnumConstants(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena);
void RegisterTypeTargets(const RtlirDesign* design, SimContext& ctx);

void RegisterClassTypeAliases(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena);
void RegisterClassScopeTypedefAliases(ClassTypeInfo* info, SimContext& ctx,
                                      Arena& arena);
void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx);
void RegisterProcessClassType(SimContext& ctx, Arena& arena);

void ShapeArrayProperties(ClassTypeInfo* info, const ClassDecl* cls,
                          const ScopeMap& scope, SimContext& ctx, Arena& arena);

void FillMultiDimLeaves(std::string_view name, const RtlirVariable& var,
                        SimContext& ctx, Arena& arena, bool in_place);
Variable* ExistingArrayElement(SimContext& ctx, const std::string& key);
Logic4Vec ArrayItemForElement(const RtlirVariable& var, const Logic4Vec& val,
                              Arena& arena);

}  // namespace delta

#endif
