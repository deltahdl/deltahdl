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

// True for the ten operators §11.4.4, §11.4.5 and §11.4.6 define: the four
// relational operators of Table 11-8, the four equality operators of
// Table 11-9 and the two wildcard equality operators of Table 11-10. Each
// compares its two operands whole and answers one bit, which is what separates
// them from the operators SynthLower::LowerBinaryBit lowers a bit at a time.
bool IsCompareOp(TokenKind op);

// True for the four operators §11.4.10 defines: the logical shifts `<<` and
// `>>` and the arithmetic shifts `<<<` and `>>>`. Each moves its left operand
// by the number of bit positions its right operand gives, so the bit of the
// result a caller asks for is built from a different bit of the left operand.
bool IsShiftOp(TokenKind op);

// One stage of a ripple-carry chain: answer `a XOR b XOR carry` and leave the
// majority of the three in `carry`. §11.4.3 addition and subtraction, the
// §11.4.2 increment and decrement operators and the §11.4.4 relational
// operators are all built from this stage, so it states the carry once.
uint32_t FullAdderBit(AigGraph& aig, uint32_t a, uint32_t b, uint32_t& carry);

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

  // §11.4.4, §11.4.5 and §11.4.6: lower one bit of a comparison. All three
  // subclauses rule that the result is 1'b0 or 1'b1, so bit 0 carries the
  // comparison and every bit above it is zero.
  uint32_t LowerCompareBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // The comparison an operator answers before the negation §11.4.4 and §11.4.5
  // define four of the ten by: `a >= b` for both `a >= b` and `a < b`, and the
  // equality of the operands for both `a == b` and `a != b`.
  uint32_t LowerCompareMatch(const Expr* expr, AigGraph& aig);

  // §11.4.6: the match of the left operand against the wildcards written into
  // the right one. Reports the expression and answers constant false when the
  // right operand is not an integer literal, since a wildcard position can only
  // be read out of a literal's own digits.
  uint32_t LowerWildcardMatch(const Expr* expr, AigGraph& aig);

  void ReportWildcardUnlowered(const Expr* expr);

  // §11.4.5: the literal that is true exactly where the two operands hold the
  // same bit at every position below `width`.
  uint32_t CompareEqual(const Expr* lhs, const Expr* rhs, AigGraph& aig,
                        uint32_t width, bool is_signed);

  // §11.4.4: the literal that is true exactly where `lhs` is at least `rhs`,
  // which is the carry out of the subtraction of the two.
  uint32_t CompareAtLeast(const Expr* lhs, const Expr* rhs, AigGraph& aig,
                          uint32_t width, bool is_signed);

  // The number of bit positions a comparison of the two operands is carried
  // out over.
  uint32_t CompareWidth(const Expr* lhs, const Expr* rhs);

  // §11.8.2: lower one bit of an operand the expression around it has
  // propagated a wider size to. The positions above the operand's own declared
  // width are extension positions, and the standard rules that an operand
  // "shall be sign-extended only if the propagated type is signed", which is
  // what `sign_extend` carries. §11.4.4 and §11.4.5 extend both operands of a
  // comparison to the width it is carried out over, and §11.4.10 extends a
  // shift's left operand to the width the shift moves it within.
  uint32_t LowerExtendedOperandBit(const Expr* expr, AigGraph& aig,
                                   uint32_t bit, bool sign_extend);

  // §11.4.10: lower one bit of `a << b`, `a >> b`, `a <<< b` or `a >>> b`. The
  // bit of the result at `bit` is a bit of the left operand at another index,
  // so this reads the left operand across the whole width the shift moves it
  // within rather than at `bit` alone.
  uint32_t LowerShiftBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // The number of bit positions a shift moves its left operand within.
  uint32_t ShiftWidth(const Expr* lhs);

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

  // §11.8.1: whether `expr` is signed, over the rules that subclause states for
  // the type of an expression. SynthLower::IsSignedSignal answers the same
  // question about one declared name, which is the leaf of this one. §11.4.10
  // fills the bit positions `>>>` vacates with the sign bit only where the type
  // of the whole expression the shift stands in is signed, so that expression
  // is what has to be read and not the shift's own left operand.
  bool IsSignedExpr(const Expr* expr);

  void RegisterOutputs(AigGraph& aig);

  Arena& arena_;
  DiagEngine& diag_;

  std::unordered_map<std::string_view, std::vector<uint32_t>> signal_bits_;

  std::unordered_map<std::string_view, uint32_t> signal_widths_;

  std::unordered_map<std::string_view, bool> signal_signed_;

  std::vector<std::pair<std::string_view, uint32_t>> output_ports_;

  // §11.8.2: the size the assignment being lowered propagates back down to the
  // context-determined operands of its right-hand side, and zero while no
  // assignment is being lowered. §11.6.1 Table 11-21 gives a shift the bit
  // length of its left operand and makes that operand context-determined, so
  // this is the width a shift moves its left operand within: `y` eight bits
  // wide makes `y = a << 1` a shift within eight positions, whatever width `a`
  // was declared.
  uint32_t propagated_width_ = 0;

  // §11.8.2: the type the assignment being lowered propagates back down to the
  // context-determined operands of its right-hand side, which the same step
  // propagates the size in propagated_width_ down with. §11.8.1 rules that the
  // type of an expression "does not depend on the left-hand side (if any)", so
  // this is the type of the right-hand side and not the type the target was
  // declared with. It is read only where propagated_width_ is non-zero, which
  // is what says an assignment is being lowered at all.
  bool propagated_signed_ = false;

  // The §11.4.3 arithmetic expressions LowerBinaryBit has already reported.
  // LowerContAssign and LowerAssignStmt ask LowerBinaryBit for one bit at a
  // time, so an unguarded report would name one expression once per bit of the
  // assignment target.
  std::unordered_set<const Expr*> reported_arith_;

  // Set by LowerStmt when it meets a statement it has no lowering for, by
  // LowerBinaryBit when it meets a §11.4.3 arithmetic operator it has no
  // lowering for, and by LowerWildcardMatch when a §11.4.6 wildcard comparison
  // has no literal to read its wildcard positions out of. Each contributes
  // nothing to the graph, so the graph no longer describes the module and Lower
  // answers with no netlist rather than with a wrong one.
  bool lowering_incomplete_ = false;
};

}  // namespace delta
