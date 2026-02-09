#pragma once

#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaboration/rtlir.h"
#include "synthesis/aig.h"

namespace delta {

/// Synthesis lowering: converts an RTLIR module into an AIG.
class SynthLower {
 public:
  SynthLower(Arena& arena, DiagEngine& diag);

  /// Lower an RTLIR module into an AIG. Returns nullptr on error.
  AigGraph* Lower(const RtlirModule* mod);

  /// Lower a single expression bit (public for pattern matching helper).
  uint32_t LowerExprBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  /// Check synthesizability (public for free-function delegation).
  bool CheckStmtSynthesizable(const Stmt* stmt);
  bool CheckExprSynthesizable(const Expr* expr);

 private:
  // Synthesizability validation.
  bool CheckSynthesizable(const RtlirModule* mod);
  bool CheckBlockStmts(const Stmt* stmt);
  bool CheckIfSynth(const Stmt* stmt);
  bool CheckCaseSynth(const Stmt* stmt);

  // Port mapping.
  void MapPorts(const RtlirModule* mod, AigGraph& aig);

  // Expression lowering helpers.
  uint32_t LowerIdentBit(std::string_view name, uint32_t bit);
  uint32_t LowerBinaryBit(const Expr* expr, AigGraph& aig, uint32_t bit);
  uint32_t LowerUnaryBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // Assignment lowering.
  void LowerContAssign(const RtlirContAssign& assign, AigGraph& aig);
  void LowerAlwaysComb(const RtlirProcess& proc, AigGraph& aig);
  void LowerAlwaysFF(const RtlirProcess& proc, AigGraph& aig);
  void LowerAlwaysLatch(const RtlirProcess& proc, AigGraph& aig);

  // Statement lowering.
  void LowerStmt(const Stmt* stmt, AigGraph& aig);
  void LowerIfStmt(const Stmt* stmt, AigGraph& aig);
  void LowerCaseStmt(const Stmt* stmt, AigGraph& aig);
  void LowerAssignStmt(const Stmt* stmt, AigGraph& aig);

  // Latch creation for sequential blocks.
  void CreateLatches(
      const std::unordered_map<std::string_view, std::vector<uint32_t>>& saved,
      AigGraph& aig);

  // MUX case bits into result map.
  void MuxCaseBits(
      std::unordered_map<std::string_view, std::vector<uint32_t>>& result,
      const std::unordered_map<std::string_view, std::vector<uint32_t>>& src,
      uint32_t match, AigGraph& aig);

  // Signal bit access.
  void SetSignalBit(std::string_view name, uint32_t bit, uint32_t lit);
  uint32_t GetSignalBit(std::string_view name, uint32_t bit);
  uint32_t SignalWidth(std::string_view name);

  // Output registration.
  void RegisterOutputs(AigGraph& aig);

  Arena& arena_;
  DiagEngine& diag_;

  // Signal → per-bit AIG literals.
  std::unordered_map<std::string_view, std::vector<uint32_t>> signal_bits_;
  // Signal widths from port/variable declarations.
  std::unordered_map<std::string_view, uint32_t> signal_widths_;
  // Output port names.
  std::vector<std::pair<std::string_view, uint32_t>> output_ports_;
};

}  // namespace delta
