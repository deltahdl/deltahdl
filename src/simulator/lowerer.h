#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace delta {

class Arena;
class DiagEngine;
class SimContext;
struct RtlirContAssign;
struct PackageDecl;
struct RtlirDesign;
struct RtlirModule;
struct RtlirProcess;
struct AssocArrayObject;
struct ClassDecl;
struct Expr;
struct RtlirVariable;
struct Variable;

class Lowerer {
 public:
  Lowerer(SimContext& ctx, Arena& arena, DiagEngine& diag);

  void Lower(const RtlirDesign* design);

 private:
  void LowerModule(const RtlirModule* mod);
  void LowerParams(const RtlirModule* mod);
  void LowerAliases(const RtlirModule* mod);
  void LowerVar(const RtlirVariable& var);
  void LowerVarInit(const RtlirVariable& var, Variable* v, uint32_t width);
  void LowerVarAggregate(const RtlirVariable& var);
  void LowerProcesses(const std::vector<RtlirProcess>& procs);
  void LowerProcess(const RtlirProcess& proc);
  void LowerContAssign(const RtlirContAssign& ca);
  void LowerClassDecl(const ClassDecl* cls);
  void LowerImports(const RtlirModule* mod);
  void LowerPackageItem(ModuleItem* item);
  PackageDecl* FindPackage(std::string_view name) const;
  void LowerDynArrayInit(const RtlirVariable& var);
  void InitAssocDefault(const Expr* init, AssocArrayObject* aa);
  void RegisterEnumForCast(const RtlirVariable& var);
  void RegisterEnumTypes(const RtlirModule* mod);
  void LowerChildModules(const RtlirModule* mod);

  SimContext& ctx_;
  Arena& arena_;
  const RtlirDesign* design_ = nullptr;
  uint32_t next_id_ = 0;
  std::string inst_prefix_;
};

}  // namespace delta
