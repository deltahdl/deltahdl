#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

namespace delta {

class Arena;
class DiagEngine;
class SimContext;
struct ModuleItem;
struct RtlirContAssign;
struct PackageDecl;
struct RtlirDesign;
struct RtlirModule;
struct RtlirProcess;
struct AssocArrayObject;
struct ClassDecl;
struct Expr;
struct RtlirModuleInst;
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
  void LowerProcesses(const std::vector<RtlirProcess>& procs, bool from_program,
                      uint32_t program_block_id);
  void LowerProcess(const RtlirProcess& proc, bool from_program,
                    uint32_t program_block_id);
  void LowerContAssign(const RtlirContAssign& ca, bool from_program);
  void LowerClassDecl(const ClassDecl* cls);
  void LowerImports(const RtlirModule* mod);
  void LowerPackageItem(ModuleItem* item);
  PackageDecl* FindPackage(std::string_view name) const;
  // §26.6: Lower the single item named `name` visible through `pkg` — either
  // a direct package item, or an item re-exported from another package.
  void LowerImportedName(PackageDecl* pkg, std::string_view name,
                         std::unordered_set<const PackageDecl*>& visited);
  // §26.6: Lower all items visible when wildcard-importing from `pkg`,
  // following any `export p::*` or `export *::*` declarations in `pkg`.
  void LowerAllImported(PackageDecl* pkg,
                        std::unordered_set<const PackageDecl*>& visited);
  void LowerDynArrayInit(const RtlirVariable& var);
  void InitAssocDefault(const Expr* init, AssocArrayObject* aa);
  void RegisterEnumForCast(const RtlirVariable& var);
  void RegisterEnumTypes(const RtlirModule* mod);
  void LowerChildModules(const RtlirModule* mod);
  // §4.9.6: Materialize a child instance's port_bindings — input/output
  // ports become implicit continuous assignments, inout ports alias the
  // local port variable onto the outside identifier so the two sides
  // share storage like a non-strength-reducing transistor.
  void LowerPortBindings(const RtlirModuleInst& inst, bool from_program);

  SimContext& ctx_;
  Arena& arena_;
  const RtlirDesign* design_ = nullptr;
  uint32_t next_id_ = 0;
  uint32_t next_program_block_id_ = 1;
  std::string inst_prefix_;
};

}  // namespace delta
