#pragma once

#include <cstdint>

namespace delta {

class Arena;
class DiagEngine;
class SimContext;
struct RtlirContAssign;
struct RtlirDesign;
struct RtlirModule;
struct RtlirProcess;

class Lowerer {
 public:
  Lowerer(SimContext& ctx, Arena& arena, DiagEngine& diag);

  void Lower(const RtlirDesign* design);

 private:
  void LowerModule(const RtlirModule* mod);
  void LowerProcess(const RtlirProcess& proc);
  void LowerContAssign(const RtlirContAssign& ca);

  SimContext& ctx_;
  Arena& arena_;
  DiagEngine& diag_;
  uint32_t next_id_ = 0;
};

}  // namespace delta
