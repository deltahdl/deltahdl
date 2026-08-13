#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>
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

  // §11.4.3: lower one bit of `a + b` or `a - b` as a ripple-carry chain over
  // both operands. Bit `bit` of a sum depends on every operand bit below it, so
  // this reads the operands at every index from zero up to `bit` rather than at
  // `bit` alone.
  uint32_t LowerAddSubBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // Report `a * b`, `a / b`, `a % b` or `a ** b` (§11.4.3) and answer true, and
  // answer false for every other operator. A reported expression sets
  // lowering_incomplete_, so Lower answers with no netlist rather than with one
  // whose bits stand for nothing the design wrote.
  bool ReportArithIfUnlowered(const Expr* expr);

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

  // Lower one of the four §11.4.2 increment and decrement operators over a
  // whole variable, and answer false for any other expression so that its
  // statement is reported rather than dropped.
  bool LowerIncDecStmt(const Expr* expr, AigGraph& aig);

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

  // The §11.4.3 arithmetic expressions LowerBinaryBit has already reported.
  // LowerContAssign and LowerAssignStmt ask LowerBinaryBit for one bit at a
  // time, so an unguarded report would name one expression once per bit of the
  // assignment target.
  std::unordered_set<const Expr*> reported_arith_;

  // Set by LowerStmt when it meets a statement it has no lowering for, and by
  // LowerBinaryBit when it meets a §11.4.3 arithmetic operator it has no
  // lowering for. Either contributes nothing to the graph, so the graph no
  // longer describes the module and Lower answers with no netlist rather than
  // with a wrong one.
  bool lowering_incomplete_ = false;
};

}  // namespace delta
