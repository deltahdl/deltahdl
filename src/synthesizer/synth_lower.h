#pragma once

#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
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
  // True where every operand of a §11.4.12 concatenation or a §11.4.12.1
  // replication is synthesizable, which is what the braces enclose and, for a
  // replication, the multiplier before them.
  bool CheckElementsSynthesizable(const Expr* expr);

  bool CheckSynthesizable(const RtlirModule* mod);
  bool CheckBlockStmts(const Stmt* stmt);
  bool CheckIfSynth(const Stmt* stmt);
  bool CheckCaseSynth(const Stmt* stmt);

  void MapPorts(const RtlirModule* mod, AigGraph& aig);

  // Clear the state left by the last module lowered, and read the parameters of
  // `mod`, which are the constants a select's index folds against.
  void ResetForModule(const RtlirModule* mod);

  // Record what the lowering has to know about one declared signal: how many
  // bits it has, whether it was declared signed, the literals its bits carry,
  // and the range §11.5.1 resolves a select on it against.
  void RecordSignal(std::string_view name, uint32_t width, bool is_signed,
                    const RtlirModule* mod);

  // Give an input port one AIG input per bit, and record an output port so
  // that RegisterOutputs can emit what drove it.
  void MapPortBits(const RtlirPort& port, AigGraph& aig);

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

  // §11.4.12: lower one bit of a concatenation. The bit of the result at `bit`
  // is a bit of whichever operand's own width spans that position, so this
  // reads the widths of the operands and not only their bits.
  uint32_t LowerConcatBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // §11.4.12.1: lower one bit of a replication, which is that many copies of
  // the concatenation it multiplies.
  uint32_t LowerReplicateBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // Lower one bit of the operands of `expr` joined as §11.4.12 joins them,
  // which is what both a concatenation and one copy of a replication are.
  uint32_t LowerElementsBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // How many bits `expr` carries, and nothing where the synthesizer cannot say.
  // §11.4.12 needs the size of every operand of a concatenation to place any of
  // them, so an operand this cannot answer for is one the concatenation has no
  // lowering for.
  std::optional<uint32_t> ExprWidth(const Expr* expr);

  // The widths of the operands of `expr` together.
  std::optional<uint32_t> ElementsWidth(const Expr* expr);

  // §11.4.12.1: the multiplier of `expr` times the width of what it replicates.
  std::optional<uint32_t> ReplicateWidth(const Expr* expr);

  // Report that `expr` has no lowering and answer no netlist for the module.
  // An expression the synthesizer builds nothing for used to leave the graph
  // carrying a constant while the run reported success.
  void ReportExprUnlowered(const Expr* expr, std::string_view message,
                           Subclause subclause);

  // §11.4.9: lower one bit of a reduction operator. The subclause gives it a
  // single-bit result, so bit 0 carries the fold across the operand's bits and
  // every bit above it is zero.
  uint32_t LowerReductionBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // §11.4.3: lower one bit of the unary minus, which §11.4.3.1 makes the
  // two's complement of the operand. Bit `bit` of it depends on every operand
  // bit below `bit`, so this reads the operand at every index up to `bit`.
  uint32_t LowerNegateBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // §11.5.1: lower one bit of a bit-select, a non-indexed part-select or an
  // indexed part-select. The bit of the result at `bit` is a bit of the
  // selected signal at an offset the declaration of that signal decides, so
  // this reads the declared range rather than taking an index for an offset.
  uint32_t LowerSelectBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  // Where a select lands in the storage of the signal it selects from. `name`
  // is that signal, `lo` is how far the least significant selected bit sits
  // above the least significant end of it, and `count` is how many bits the
  // select addresses. `count` is zero where the select does not resolve: its
  // base is not a signal this module declares, or an index of it did not fold
  // to a constant. `lo` is signed because §11.5.1 lets a part-select run off
  // the end of the vector, and the bits that do so read as zero here rather
  // than wrapping onto bits that are in range.
  struct SelectStorage {
    std::string_view name;
    int64_t lo = 0;
    uint32_t count = 0;
  };

  // §11.5.1: the storage `sel` addresses, resolved against the declared range
  // of its base.
  SelectStorage ResolveSelect(const Expr* sel);

  // True where `sel` addresses a bit of a vector, which is what §11.5.1
  // defines, rather than an element of an unpacked array, which is §11.5.2.
  bool IsVectorSelect(const Expr* sel);

  // Install the scope the indices of the item being lowered are folded in:
  // the module's parameters, and the §27.4 loop index values `consts` carries.
  void SetGenScope(const GenBlockConsts& consts);

  // §11.5.1: lower one bit of a select whose index did not fold, which is the
  // form the subclause writes `dword[8*sel +: 8]` and `vect[addr]` in. Such a
  // select chooses among the bits of its base rather than renaming them, so it
  // is a multiplexer over every index the declared range holds.
  uint32_t LowerVariableSelectBit(const Expr* expr, AigGraph& aig,
                                  uint32_t bit);

  // The literal that is true exactly where `expr` carries the value `value`.
  uint32_t ExprEqualsValue(const Expr* expr, AigGraph& aig, int64_t value);

  // How many bits a select whose index did not fold addresses, and zero where
  // it addresses none this builds anything for.
  int64_t VariableSelectWidth(const Expr* expr);

  // The index that carries result bit `bit` of `expr` when its index carries
  // `value`, over a select `width` bits wide.
  int64_t VariableSelectIndex(const Expr* expr, int64_t value, int64_t width,
                              uint32_t bit);

  // The declared range the indices of a select on `base` are resolved against.
  DeclaredPackedRange BaseRange(const Expr* base);

  // Drive the storage a select target addresses from `rhs`, and leave the other
  // bits of the signal as they stand. §11.5.1 rules that a part-select written
  // to "shall ... only affect the bits that are in range", so the bits outside
  // the select keep what drove them.
  void LowerSelectTarget(const Expr* lhs, const Expr* rhs, AigGraph& aig);

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

  // §11.5.1: the declared range of each signal, which is what a select on that
  // signal resolves its indices against. A width cannot answer the question,
  // because `[15:0]` and `[2:17]` are both sixteen bits wide and one value of
  // an index reaches a different bit of each.
  std::unordered_map<std::string_view, DeclaredPackedRange> signal_ranges_;

  // The signals declared with an unpacked dimension. §11.5.2 addresses an array
  // element and §11.5.1 addresses a bit of a vector, and the two are written
  // alike, so the declaration is what tells them apart. Nothing here lowers
  // §11.5.2, and a select on one of these names is left alone rather than
  // resolved against the packed range of its element type.
  std::unordered_set<std::string_view> unpacked_arrays_;

  // The resolved parameters of the module being lowered, which is the scope a
  // select's index is folded in. §11.5.1 rules that a non-indexed part-select
  // is written with constant integer expressions, and a parameter is what such
  // an expression is usually written from.
  ScopeMap param_scope_;

  // §27.4 gives each instance of a loop generate block an implicit localparam
  // named after the loop index, and the elaborator leaves that name unfolded in
  // the body it shares between the instances. This is param_scope_ with the
  // values of the assignment being lowered added, so `assign out[i] = in[i];`
  // resolves `i` to the value its own instance was elaborated with.
  ScopeMap scope_;

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

  // The expressions ReportExprUnlowered has already reported: the §11.4.3
  // arithmetic operators, and the §11.4.12 concatenations and §11.4.12.1
  // replications whose operand widths it cannot answer. LowerContAssign and
  // LowerAssignStmt ask for one bit at a time, so an unguarded report would
  // name one expression once per bit of the assignment target.
  std::unordered_set<const Expr*> reported_exprs_;

  // Set by LowerStmt when it meets a statement it has no lowering for, by
  // LowerBinaryBit when it meets a §11.4.3 arithmetic operator it has no
  // lowering for, and by LowerWildcardMatch when a §11.4.6 wildcard comparison
  // has no literal to read its wildcard positions out of. Each contributes
  // nothing to the graph, so the graph no longer describes the module and Lower
  // answers with no netlist rather than with a wrong one.
  bool lowering_incomplete_ = false;
};

}  // namespace delta
