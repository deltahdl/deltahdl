#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

class Arena;
class DiagEngine;
class SimContext;
struct ImportItem;
struct ModuleItem;
struct RtlirContAssign;
struct RtlirUdpInst;
struct PackageDecl;
struct RtlirDesign;
struct Expr;

using ClockReads = std::pair<std::vector<EventExpr>, std::vector<const Expr*>>;
struct RtlirModule;
struct RtlirProcess;
struct ProceduralCheckerAssertion;
struct AssocArrayObject;
struct QueueObject;
struct ClassDecl;
struct ClassTypeInfo;
struct Expr;
struct RtlirModuleInst;
struct RtlirPortBinding;
struct RtlirVariable;
struct Variable;
struct Process;

void ScheduleProcess(Process* proc, SimContext& ctx);

const RtlirGenBlockSubroutine* DeclaringGenBlock(const ModuleItem* func,
                                                 const RtlirModule* mod);

struct SpecifyScope {
  std::string inst_prefix;
  const RtlirModule* module;
};

struct AssertionSampleScope {
  std::string inst_prefix;
  std::vector<std::string> names;
};

struct StaticLocalOwner {
  std::string inst_prefix;
  const ModuleItem* subroutine = nullptr;
  const RtlirGenBlockSubroutine* gen_block = nullptr;
  const Process* process = nullptr;
  const Stmt* body = nullptr;
  const std::vector<ClassDecl*>* classes = nullptr;
};

class Lowerer {
 public:
  Lowerer(SimContext& ctx, Arena& arena, DiagEngine& diag);

  void Lower(const RtlirDesign* design);

 private:
  void LowerModule(const RtlirModule* mod);
  void LowerParallelTop(const RtlirModule* mod);
  void LowerTopNamedBy(const Expr* conn);
  void LowerParams(const RtlirModule* mod);
  void LowerParam(const RtlirModule& mod, const RtlirParamDecl& p,
                  std::string_view full);
  void FillParamValue(const RtlirParamDecl& p, std::function<void()> fill);
  void FillInValueScope(const RtlirParamDecl& p,
                        const std::function<void()>& fill);
  void RegisterGenBlockMembers(const RtlirModule* mod);
  void LowerAliases(const RtlirModule* mod);
  void LowerModuleProcesses(const RtlirModule* mod);
  const std::vector<EventExpr>& ClockOf(const RtlirProcess& proc);
  void LowerVar(std::string_view name, const RtlirVariable& var);
  void LowerVarInit(std::string_view name, const RtlirVariable& var,
                    Variable* v, uint32_t width);
  Logic4Vec CoerceVarInitValue(const RtlirVariable& var, Logic4Vec val,
                               uint32_t width);
  void LowerVarAggregate(std::string_view name, const RtlirVariable& var);
  void LowerProcesses(const std::vector<RtlirProcess>& procs, bool from_program,
                      uint32_t program_block_id);
  void LowerProcess(const RtlirProcess& proc, bool from_program,
                    uint32_t program_block_id);
  void InstallGenBlockConsts(const GenBlockConsts& consts, Process* p);
  void RecordStaticLocalSubroutines(const RtlirModule* mod);
  void RecordStaticLocalProcess(const Process* p, const Stmt* body);
  void MakeNamedSpecializations();
  void InitializeStaticLocals();
  void LowerContAssign(const RtlirContAssign& ca, bool from_program);
  void LowerBidirSwitch(const RtlirBidirSwitch& sw, bool from_program);
  void LowerUdpInst(const RtlirUdpInst& inst, bool from_program);
  void LowerSequenceMonitors(const RtlirModule* mod);
  void LowerSampledClockMonitors(const Stmt* body);
  void LowerSequenceMonitor(const ModuleItem* seq, std::string_view ep_name,
                            const std::vector<EventExpr>* context_clock);
  void CreateEndPoint(std::string_view ep_name);
  void LowerFreeVariableSolver(const RtlirModule* mod);
  void LowerNamedSequenceMonitor(const ModuleItem* seq,
                                 const std::vector<EventExpr>* first_clock,
                                 const std::vector<ClockReads>& further);
  void LowerClassDecl(const ClassDecl* cls,
                      const std::vector<ModuleItem*>& scope_items);
  void RegisterClassDecl(const ClassDecl* cls,
                         const std::vector<ModuleItem*>& scope_items);
  void InitClassStaticProperties(const ClassDecl* cls);
  std::vector<const ClassDecl*> RegisterChildClasses(const RtlirModule* mod);
  std::string_view DeclaringPackage(const ClassDecl* cls) const;
  void LowerImports(const RtlirModule* mod);
  void LowerCompilationUnitImports();
  void LowerCompilationUnitClasses();
  void LowerDesignData();
  void InitCompilationUnitData();
  void ConstructDesignData();
  void LowerUnimportedPackageClasses();
  void LowerUnimportedClassesOf(const PackageDecl* pkg);
  void LowerUnitClassPackageBases();
  void LowerPackageClass(const PackageDecl* pkg, const ClassDecl* cls);
  void AliasExportedClassKeys(const PackageDecl* pkg, const ClassDecl* cls);
  void LowerPackageItem(const PackageDecl* pkg, ModuleItem* item);
  void LowerOneImport(const ImportItem& imp);
  void LowerUnitImportItems(const std::vector<ModuleItem*>& items);
  PackageDecl* FindPackage(std::string_view name) const;

  void LowerImportedName(PackageDecl* pkg, std::string_view name,
                         std::unordered_set<const PackageDecl*>& visited);

  void LowerAllImported(PackageDecl* pkg,
                        std::unordered_set<const PackageDecl*>& visited);

  void AliasPackageDataItem(const PackageDecl* pkg, const ModuleItem* item);
  void AliasAllPackageDataItems(const PackageDecl* pkg);
  void AliasNamedPackageDataItem(const PackageDecl* pkg,
                                 std::string_view item_name);
  bool AliasPackageEnumMember(const PackageDecl* pkg, std::string_view name);
  void AliasImportedPackageName(std::string_view name, std::string_view qname);
  void LowerDynArrayInit(QueueObject* q, const RtlirVariable& var);
  void InitAssocDefault(const Expr* init, AssocArrayObject* aa);
  void RegisterEnumForCast(std::string_view name, const RtlirVariable& var);
  void RegisterEnumTypes(const RtlirModule* mod);
  void RegisterParamEnumTypes(const RtlirModule* mod);
  void RecordSpecifyScope(const RtlirModule* mod);
  void RecordAssertionSampleScope(const RtlirProcess& proc);
  void RecordAssertionSampleScope(const Stmt* body);
  void RecordSubroutineAssertionSampleScopes(const RtlirModule* mod);
  void RegisterDesignAssertionSampling();
  void RegisterDesignTiming();
  bool KeepProceduralCheckerAssertion(const RtlirProcess& proc);
  void RecordProceduralCheckerActuals(const RtlirModuleInst& inst,
                                      const std::string& child_prefix);
  void RecordCheckerInstantiations(const RtlirProcess& proc, Process* p);
  void LinkCheckerInstantiations();
  void LowerChildBodyUnderCheckerRoot(const RtlirModuleInst& child);
  void LowerChildModules(const RtlirModule* mod);
  void RegisterChildInstanceKeys(const RtlirModule* mod);
  void LowerChildInstance(const RtlirModuleInst& child);
  void LowerChildBody(const RtlirModule* mod);
  void LowerClockingBlocks(const RtlirModule* mod);
  void AttachDesignClocking();
  void CreateChildModuleVariables(const std::string& inst_prefix,
                                  const RtlirModule* resolved);

  void LowerPortBindings(const RtlirModuleInst& inst, bool from_program);
  void RecordCheckerActualSampleScope(const RtlirModuleInst& inst);
  void RecordCheckerInstanceScopes(const RtlirModuleInst& inst,
                                   const std::string& inst_seg);
  bool LowerArrayPortBinding(const RtlirModuleInst& inst,
                             const RtlirPortBinding& binding,
                             const std::string& inst_seg, bool from_program);
  bool TryAliasInterfacePort(const RtlirModuleInst& inst,
                             const RtlirPortBinding& binding);
  bool AliasInterfaceArrayPort(const RtlirModuleInst& inst,
                               const RtlirPortBinding& binding,
                               const RtlirPort& port,
                               const std::string& port_key);
  void AliasInterfacePortTo(const RtlirModuleInst& inst,
                            const RtlirPortBinding& binding,
                            const RtlirModule* ifc, const std::string& port_key,
                            const std::string& instance);
  void DrivePathDelayedMembers(const RtlirModuleInst& inst,
                               std::string_view port_name,
                               const RtlirModule* ifc,
                               const std::string& port_prefix,
                               const std::string& instance);
  std::string ConnectedInstancePath(std::string_view name) const;
  std::string ConnectedInstanceKey(std::string_view name) const;
  const RtlirModule* ConnectedInterface(const RtlirPort& port, const Expr* conn,
                                        std::string& instance) const;
  void RegisterModportExpressions(const RtlirPort& port, const Expr* conn,
                                  const RtlirModule* ifc,
                                  const std::string& port_key,
                                  const std::string& instance_key);
  void RegisterExportedSubroutines(const RtlirModuleInst& inst,
                                   std::string_view port_name,
                                   const RtlirModule* ifc,
                                   const std::string& instance_key);

  SimContext& ctx_;
  Arena& arena_;
  const RtlirDesign* design_ = nullptr;
  uint32_t next_id_ = 0;
  uint32_t next_program_block_id_ = 1;
  std::string inst_prefix_;
  const RtlirModule* port_parent_ = nullptr;
  const RtlirModule* importing_module_ = nullptr;
  std::string_view import_scope_prefix_;
  std::vector<SpecifyScope> specify_scopes_;
  std::vector<AssertionSampleScope> assertion_sample_scopes_;
  std::vector<StaticLocalOwner> static_local_owners_;
  std::vector<StaticLocalOwner> specializing_code_;
  bool lowering_checker_ = false;
  bool interconnect_annotatable_ = false;
  std::string procedural_checker_root_;
  RtlirModuleInst top_inst_;
  const RtlirModuleInst* lowering_inst_ = &top_inst_;
  std::unordered_map<std::string, ActualsByFormal> procedural_checker_actuals_;
  std::unordered_map<std::string, std::string> checker_parent_prefixes_;
  std::unordered_map<std::string,
                     std::vector<const ProceduralCheckerAssertion*>>
      procedural_checker_assertions_;
  struct CheckerInstantiationLink {
    Process* process = nullptr;
    const Stmt* stmt = nullptr;
    std::string inst_prefix;
  };
  std::vector<CheckerInstantiationLink> checker_instantiation_links_;
  std::vector<std::string> interface_instance_prefixes_;
  void EnrollInterfaceMembers(std::string_view name,
                              const std::string& scope_prefix);
  void EnrollArrayElements(const std::string& name);
  std::unordered_set<std::string> path_delayed_ports_;
  std::unordered_map<const RtlirModule*, std::string> instance_prefixes_;
  std::vector<std::function<void()>> deferred_param_fills_;
};

}  // namespace delta
