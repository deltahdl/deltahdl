#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

struct RtlirModule;
struct ClassDecl;

void PromoteSequenceInstancesInProperties(const ModuleDecl* decl,
                                          const PropertyRegistry& registry,
                                          Arena& arena);

void SubstituteBooleanSpec(ModuleItem* item, Arena& arena);

void RegisterClassParams(CompilationUnit* unit, ScopeMap& cu_param_scope,
                         Arena& arena, DiagEngine& diag);

void RegisterModuleClassParams(const ClassDecl* cls,
                               const ScopeMap& module_scope,
                               ScopeMap& cu_param_scope, Arena& arena,
                               DiagEngine& diag);

struct ImportedEnumCtx {
  const CompilationUnit* unit;
  Arena& arena;
  TypedefMap& typedefs;
  std::unordered_set<std::string_view>& enum_member_names;
};

void RegisterImportedEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                                  const ImportedEnumCtx& ctx);

void RegisterCuEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                            const ImportedEnumCtx& ctx);

bool BindIntroducesName(const CompilationUnit* unit, std::string_view module,
                        std::string_view inst, std::string_view name);

NetType DataTypeToNetType(DataTypeKind kind);

NetType WrittenNetType(const DataType& dtype);

void ResolveFormalAggregateTypes(ModuleItem* item, const TypedefMap& typedefs,
                                 Arena& arena);

void ResolveClassMethodFormalTypes(ClassDecl* cls, const TypedefMap& outer,
                                   Arena& arena);

void ResolveModuleClassFormalTypes(const std::vector<ClassDecl*>& classes,
                                   const TypedefMap& typedefs, Arena& arena);

void ResolveModuleSubroutineFormalTypes(const std::vector<ModuleItem*>& items,
                                        const TypedefMap& typedefs,
                                        Arena& arena);

void ResolveUnitScopeFormalTypes(CompilationUnit* unit,
                                 const TypedefMap& typedefs, Arena& arena);

bool IsNameDeclared(std::string_view name, const RtlirModule* mod);
bool PortSelectsFrom(const RtlirPort& port, std::string_view name);

bool IsConditionalGenerateConstruct(ModuleItemKind k);

uint32_t GateTerminalWidth(const Expr* t, const RtlirModule* mod,
                           const ScopeMap& scope);

Expr* GateTerminalBit(Expr* t, uint32_t bit, const RtlirModule* mod,
                      const ScopeMap& scope, Arena& arena);

void ReportUndeclaredLoopGenvars(const ModuleDecl* decl, DiagEngine& diag);

void AssignUnitGenerateBlockNames(const CompilationUnit* unit, Arena& arena);

bool IsDirectlyNestedBlock(const std::vector<ModuleItem*>& body,
                           bool has_begin_end);

std::unordered_map<std::string_view, const ClassDecl*> BuildParamClassRegistry(
    const CompilationUnit* unit);

struct SpecparamNameSets {
  std::unordered_set<std::string_view>& specparams;
  std::unordered_set<std::string_view>& constants;
};
void RegisterSpecifyBlockSpecparams(const ModuleItem* item, RtlirModule* mod,
                                    const TypedefMap& typedefs,
                                    SpecparamNameSets names, DiagEngine& diag);

uint32_t SpecparamWidth(const DataType& type, const Expr* init,
                        const TypedefMap& typedefs);

bool SpecparamIsReal(const DataType& type, const Expr* init);

void CheckCheckerBodyItemRules(const ModuleItem* item, const ModuleDecl* decl,
                               bool parent_is_checker, DiagEngine& diag);

std::vector<ModuleItem*> TimingCheckDelayedSignalItems(const ModuleDecl* decl,
                                                       Arena& arena);

void ValidateDriveStrengthHasAssignment(const ModuleItem* item,
                                        DiagEngine& diag);

}  // namespace delta
