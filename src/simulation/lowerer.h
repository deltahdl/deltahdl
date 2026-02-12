#pragma once

#include <cstdint>
#include <vector>

namespace delta {

class Arena;
class DiagEngine;
class SimContext;
struct RtlirContAssign;
struct RtlirDesign;
struct RtlirModule;
struct RtlirProcess;
struct AssocArrayObject;
struct ClassDecl;
struct Expr;
struct RtlirVariable;

class Lowerer {
 public:
  Lowerer(SimContext& ctx, Arena& arena, DiagEngine& diag);

  void Lower(const RtlirDesign* design);

 private:
  void LowerModule(const RtlirModule* mod);
  void LowerVar(const RtlirVariable& var);
  void LowerVarAggregate(const RtlirVariable& var);
  void LowerProcesses(const std::vector<RtlirProcess>& procs);
  void LowerProcess(const RtlirProcess& proc);
  void LowerContAssign(const RtlirContAssign& ca);
  void LowerClassDecl(const ClassDecl* cls);
  void InitAssocDefault(const Expr* init, AssocArrayObject* aa);
  void RegisterEnumForCast(const RtlirVariable& var);
  void RegisterEnumTypes(const RtlirModule* mod);

  SimContext& ctx_;
  Arena& arena_;
  uint32_t next_id_ = 0;
};

}  // namespace delta
