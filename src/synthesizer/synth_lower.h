#pragma once

#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "synthesizer/aig.h"

namespace delta {

class SynthLower {
 public:
  SynthLower(Arena& arena, DiagEngine& diag);

  AigGraph* Lower(const RtlirModule* mod);

  uint32_t LowerExprBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  bool CheckStmtSynthesizable(const Stmt* stmt);
  bool CheckExprSynthesizable(const Expr* expr);

 private:
  bool CheckSynthesizable(const RtlirModule* mod);
  bool CheckBlockStmts(const Stmt* stmt);
  bool CheckIfSynth(const Stmt* stmt);
  bool CheckCaseSynth(const Stmt* stmt);

  void MapPorts(const RtlirModule* mod, AigGraph& aig);

  uint32_t LowerIdentBit(std::string_view name, uint32_t bit);
  uint32_t LowerBinaryBit(const Expr* expr, AigGraph& aig, uint32_t bit);
  uint32_t LowerUnaryBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // §10.7: lower one bit of an assignment right-hand side in the context of the
  // target width. Bits above the RHS's own width are extension bits: the RHS
  // sign bit when the RHS is signed, otherwise zero.
  uint32_t LowerAssignRhsBit(const Expr* rhs, AigGraph& aig, uint32_t bit);

  void LowerContAssign(const RtlirContAssign& assign, AigGraph& aig);
  void LowerAlwaysComb(const RtlirProcess& proc, AigGraph& aig);
  void LowerAlwaysFF(const RtlirProcess& proc, AigGraph& aig);
  void LowerAlwaysLatch(const RtlirProcess& proc, AigGraph& aig);

  void LowerStmt(const Stmt* stmt, AigGraph& aig);
  void LowerIfStmt(const Stmt* stmt, AigGraph& aig);
  void LowerCaseStmt(const Stmt* stmt, AigGraph& aig);
  void LowerAssignStmt(const Stmt* stmt, AigGraph& aig);

  void CreateLatches(
      const std::unordered_map<std::string_view, std::vector<uint32_t>>& saved,
      AigGraph& aig);

  void MuxCaseBits(
      std::unordered_map<std::string_view, std::vector<uint32_t>>& result,
      const std::unordered_map<std::string_view, std::vector<uint32_t>>& src,
      uint32_t match, AigGraph& aig);

  void SetSignalBit(std::string_view name, uint32_t bit, uint32_t lit);
  uint32_t GetSignalBit(std::string_view name, uint32_t bit);
  uint32_t SignalWidth(std::string_view name);
  bool IsSignedSignal(std::string_view name);

  void RegisterOutputs(AigGraph& aig);

  Arena& arena_;
  DiagEngine& diag_;

  std::unordered_map<std::string_view, std::vector<uint32_t>> signal_bits_;

  std::unordered_map<std::string_view, uint32_t> signal_widths_;

  std::unordered_map<std::string_view, bool> signal_signed_;

  std::vector<std::pair<std::string_view, uint32_t>> output_ports_;
};

}  // namespace delta
