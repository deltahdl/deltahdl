#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/types.h"
// GenBlockConsts, the §27.4 loop-index values a lowered thread carries.
#include "elaborator/rtlir.h"

namespace delta {

class Arena;
class DiagEngine;
class SimContext;
struct ModuleItem;
struct RtlirContAssign;
struct RtlirUdpInst;
struct PackageDecl;
struct RtlirDesign;
struct RtlirModule;
struct RtlirProcess;
struct AssocArrayObject;
struct QueueObject;
struct ClassDecl;
struct Expr;
struct RtlirModuleInst;
struct RtlirPortBinding;
struct RtlirVariable;
struct Variable;
struct Process;

// §4.4: puts a lowered process on the scheduler, as an evaluation event at
// time zero in the process's own region, so that it runs once when the
// simulation starts. Every kind of process is started this way -- the
// structured procedures of §9.2 and the continuous assignments of §10.3 alike
// -- which is why it is declared here rather than kept file-local:
// src/simulator/lowerer.cpp defines it and src/simulator/lowerer_contassign.cpp
// is its second caller.
void ScheduleProcess(Process* proc, SimContext& ctx);

class Lowerer {
 public:
  Lowerer(SimContext& ctx, Arena& arena, DiagEngine& diag);

  void Lower(const RtlirDesign* design);

 private:
  void LowerModule(const RtlirModule* mod);
  void LowerParams(const RtlirModule* mod);
  void LowerAliases(const RtlirModule* mod);
  // Creates the storage a variable declaration states, keyed under `name`.
  // `name` is the name the storage is reachable by, which is the declared name
  // at the top of the hierarchy and the instance-prefixed form under an
  // instance; every property recorded here is recorded against it, so a
  // declaration states the same thing wherever in the hierarchy it sits. The
  // maps hold `name` rather than a copy, so a name built at run time must be
  // interned in the arena before it is passed.
  void LowerVar(std::string_view name, const RtlirVariable& var);
  void LowerVarInit(std::string_view name, const RtlirVariable& var,
                    Variable* v, uint32_t width);
  // §6.11.2/§6.12.1: applies the implicit conversions a declaration
  // initializer undergoes as an assignment to its declared variable.
  Logic4Vec CoerceVarInitValue(const RtlirVariable& var, Logic4Vec val,
                               uint32_t width);
  void LowerVarAggregate(std::string_view name, const RtlirVariable& var);
  void LowerProcesses(const std::vector<RtlirProcess>& procs, bool from_program,
                      uint32_t program_block_id);
  void LowerProcess(const RtlirProcess& proc, bool from_program,
                    uint32_t program_block_id);
  void InstallGenBlockConsts(const GenBlockConsts& consts, Process* p);
  void LowerContAssign(const RtlirContAssign& ca, bool from_program);
  // §29.8: creates the process that drives one user-defined primitive
  // instance's output terminal from the state table §29.3.4 defines.
  // `from_program` says the instance sits in a program, whose drives are
  // reactive (§24.3.1); LowerContAssign takes it for the same reason, since
  // §29.8 instantiates a UDP "in the same manner as gates". Defined in
  // src/simulator/lowerer_udp.cpp.
  void LowerUdpInst(const RtlirUdpInst& inst, bool from_program);
  void LowerSequenceMonitors(const RtlirModule* mod);
  void LowerClassDecl(const ClassDecl* cls);
  void LowerImports(const RtlirModule* mod);
  void LowerPackageItem(ModuleItem* item);
  PackageDecl* FindPackage(std::string_view name) const;

  void LowerImportedName(PackageDecl* pkg, std::string_view name,
                         std::unordered_set<const PackageDecl*>& visited);

  void LowerAllImported(PackageDecl* pkg,
                        std::unordered_set<const PackageDecl*>& visited);

  // §26.3: binds one imported parameter or variable of `pkg` under its
  // unqualified spelling in the scope whose imports are being lowered, which is
  // the instance inst_prefix_ names. The other two walk a whole package for a
  // wildcard import and one named item for an explicit one.
  void AliasPackageDataItem(const PackageDecl* pkg, const ModuleItem* item);
  void AliasAllPackageDataItems(const PackageDecl* pkg);
  void AliasNamedPackageDataItem(const PackageDecl* pkg,
                                 std::string_view item_name);
  void LowerDynArrayInit(QueueObject* q, const RtlirVariable& var);
  void InitAssocDefault(const Expr* init, AssocArrayObject* aa);
  void RegisterEnumForCast(std::string_view name, const RtlirVariable& var);
  void RegisterEnumTypes(const RtlirModule* mod);
  void LowerChildModules(const RtlirModule* mod);
  void CreateChildModuleVariables(const std::string& inst_prefix,
                                  const RtlirModule* resolved);

  void LowerPortBindings(const RtlirModuleInst& inst, bool from_program);
  bool TryAliasInterfacePort(const RtlirModuleInst& inst,
                             const RtlirPortBinding& binding);

  SimContext& ctx_;
  Arena& arena_;
  const RtlirDesign* design_ = nullptr;
  uint32_t next_id_ = 0;
  uint32_t next_program_block_id_ = 1;
  std::string inst_prefix_;
};

}  // namespace delta
