#include "synthesizer/synth_lower.h"

#include <string>
#include <string_view>

#include "elaborator/elaborator_helpers.h"
#include "synthesizer/synth_pattern.h"

namespace delta {

SynthLower::SynthLower(Arena& arena, DiagEngine& diag)
    : arena_(arena), diag_(diag) {}

// What a §11.4.3 arithmetic operator is called in Table 11-3, for the four this
// synthesizer reports rather than lowers. An operator it lowers has no entry
// and comes back with an empty message.
//
// The four are reported because an AIG holds two values per node and §11.4.3
// rules that `a / b` and `a % b` yield x throughout when b is zero, which the
// graph has no literal for. `a * b` and `a ** b` are here because no chain has
// been written for them, not because of the x rule.
static NonSynthRule NonSynthArithRule(TokenKind op) {
  switch (op) {
    case TokenKind::kStar:
      return {"'a * b', a multiplied by b, has no lowering in the synthesizer",
              "11.4.3"};
    case TokenKind::kSlash:
      return {"'a / b', a divided by b, has no lowering in the synthesizer",
              "11.4.3"};
    case TokenKind::kPercent:
      return {"'a % b', a modulo b, has no lowering in the synthesizer",
              "11.4.3"};
    case TokenKind::kPower:
      return {
          "'a ** b', a to the power of b, has no lowering in the "
          "synthesizer",
          "11.4.3"};
    default:
      return {};
  }
}

// What an expression kind this synthesizer has no lowering for is called in
// IEEE 1800-2023, and the subclause that defines it. A kind LowerExprBit lowers
// has no entry and comes back with an empty message.
//
// Each is a construct the standard defines rather than a gap with no name, so
// each names its own subclause as NonSynthArithRule does, rather than
// Subclause::None(). Answering one of these with a constant contributes a bit
// the design did not write, which is why the entry exists at all.
NonSynthRule NonSynthExprRule(ExprKind kind) {
  switch (kind) {
    case ExprKind::kRealLiteral:
      return {"a real literal constant has no lowering in the synthesizer",
              "5.7.2"};
    case ExprKind::kTimeLiteral:
      return {"a time literal has no lowering in the synthesizer", "5.8"};
    case ExprKind::kStringLiteral:
      return {"a string literal expression has no lowering in the synthesizer",
              "11.10"};
    case ExprKind::kSystemCall:
      return {
          "a system task or system function has no lowering in the "
          "synthesizer",
          "5.6.3"};
    // ExprKind::kMemberAccess has no entry here, and
    // SynthLower::DottedNameRule in synth_lower_dotted_name.cpp answers for
    // it instead. §23.7 states that a hierarchical name and a
    // member select "share the same syntactic form of a sequence of name
    // components separated by periods", and that which one a dotted name is
    // depends on what its first component names -- a scope, or a data object.
    // That question is about the module the name was written in, which this
    // free function cannot read.
    case ExprKind::kCall:
      return {"a function call has no lowering in the synthesizer", "13.4"};
    case ExprKind::kAssignmentPattern:
      return {"an assignment pattern has no lowering in the synthesizer",
              "10.9"};
    case ExprKind::kCast:
      return {"a cast has no lowering in the synthesizer", "6.24.1"};
    case ExprKind::kTypeRef:
      return {"the type operator has no lowering in the synthesizer", "6.23"};
    case ExprKind::kPostfixUnary:
      return {
          "a postfix increment or decrement operator written inside an "
          "expression has no lowering in the synthesizer",
          "11.4.2"};
    case ExprKind::kInside:
      return {"the set membership operator has no lowering in the synthesizer",
              "11.4.13"};
    case ExprKind::kStreamingConcat:
      return {"a streaming operator has no lowering in the synthesizer",
              "11.4.14"};
    case ExprKind::kMinTypMax:
      return {
          "a minimum, typical, and maximum delay expression has no "
          "lowering in the synthesizer",
          "11.11"};
    case ExprKind::kTagged:
      return {"a tagged union expression has no lowering in the synthesizer",
              "11.9"};
    default:
      return {};
  }
}

// The first initial or final procedure the module declares, or null when it
// declares neither. Which one comes first decides where the report below
// stands, so a module holding several is reported at one it actually holds.
static const RtlirProcess* FirstInitialOrFinal(const RtlirModule* mod) {
  for (const auto& proc : mod->processes) {
    if (proc.kind == RtlirProcessKind::kInitial ||
        proc.kind == RtlirProcessKind::kFinal) {
      return &proc;
    }
  }
  return nullptr;
}

// Reject a procedure that describes no hardware, in the words of the subclause
// that defines it. An initial procedure and a final procedure are separate
// constructs of the standard, so one sentence covering both would leave a
// reader unable to tell which of the two the module actually holds.
static void ReportUnsynthesizableProcedure(const RtlirProcess& proc,
                                           DiagEngine& diag) {
  if (proc.kind == RtlirProcessKind::kFinal) {
    diag.Error(proc.loc, "final procedure is not synthesizable",
               Subclause("9.2.3"));
    return;
  }
  diag.Error(proc.loc, "initial procedure is not synthesizable",
             Subclause("9.2.1"));
}

// True if any event-control term carries an edge qualifier (posedge/negedge/
// edge) — i.e. the block is edge-sensitive (sequential) rather than level.
static bool SensitivityHasEdge(const RtlirProcess& proc) {
  for (const auto& ev : proc.sensitivity) {
    if (ev.edge == Edge::kPosedge || ev.edge == Edge::kNegedge ||
        ev.edge == Edge::kEdge)
      return true;
  }
  return false;
}

// True if any event-control term carries an `iff` qualifier (§9.4.2.3). A
// level-sensitive `always` whose trigger is gated by `iff` only updates when
// the guard holds, which synthesizes to a latch.
static bool SensitivityHasIff(const RtlirProcess& proc) {
  for (const auto& ev : proc.sensitivity) {
    if (ev.iff_condition) return true;
  }
  return false;
}

bool SynthLower::CheckSynthesizable(const RtlirModule* mod) {
  const RtlirProcess* initial_final = FirstInitialOrFinal(mod);
  bool has_synth_content = !mod->assigns.empty();
  for (const auto& proc : mod->processes) {
    if (proc.kind == RtlirProcessKind::kInitial ||
        proc.kind == RtlirProcessKind::kFinal) {
      continue;
    }
    has_synth_content = true;
    if (const Expr* ev = NamedEventTerm(proc.sensitivity, mod)) {
      diag_.Error(ev->range.start,
                  "named event in event control is not synthesizable",
                  Subclause("15.5.2"));
      return false;
    }
    if (!CheckStmtSynthesizable(proc.body, mod)) return false;
  }
  // An initial procedure executes once and a final procedure executes at the
  // end of simulation time, so neither describes hardware. Either is tolerated
  // (bypassed) when the module also describes synthesizable logic, but a
  // module whose only content is one of them has nothing to synthesize.
  if (initial_final && !has_synth_content) {
    ReportUnsynthesizableProcedure(*initial_final, diag_);
    return false;
  }
  return true;
}

void SynthLower::ResetForModule(const RtlirModule* mod) {
  signal_bits_.clear();
  signal_widths_.clear();
  signal_signed_.clear();
  signal_ranges_.clear();
  unpacked_arrays_.clear();
  array_shapes_.clear();
  output_ports_.clear();
  reported_exprs_.clear();
  literal_bits_.clear();
  propagated_width_ = 0;
  propagated_signed_ = false;
  lowering_incomplete_ = false;

  // The scope a select's index folds in. §6.20.2 makes a parameter a constant
  // known at elaboration, and the elaborator has already resolved each one, so
  // a bound written `[W-1:0]` and an index written `[W-1]` both fold here.
  param_scope_.clear();
  for (const auto& param : mod->params) {
    if (param.is_resolved) param_scope_[param.name] = param.resolved_value;
  }
  scope_ = param_scope_;
}

void SynthLower::RecordSignal(std::string_view name, uint32_t width,
                              bool is_signed, const RtlirModule* mod) {
  signal_widths_[name] = width;
  signal_signed_[name] = is_signed;
  signal_bits_[name].resize(width, AigGraph::kConstFalse);
  // §11.5.1 resolves a select against the declaration of what it selects from,
  // so the declared range is recorded beside the width. It is read once per
  // signal rather than once per select, because SignalDeclaredRange searches
  // the module's variables, nets and ports by name.
  signal_ranges_[name] = SignalDeclaredRange(name, mod, param_scope_);
}

void SynthLower::MapPortBits(const RtlirPort& port, uint32_t width,
                             AigGraph& aig) {
  if (port.direction == Direction::kInput) {
    auto& bits = signal_bits_[port.name];
    for (uint32_t b = 0; b < width; ++b) {
      bits[b] = aig.AddInput();
    }
    return;
  }
  if (port.direction == Direction::kOutput) {
    output_ports_.emplace_back(port.name, width);
  }
}

void SynthLower::MapPorts(const RtlirModule* mod, AigGraph& aig) {
  for (const auto& port : mod->ports) {
    RecordArrayShape(port.name, port.width, port.num_unpacked_dims,
                     port.unpacked_dims);
    uint32_t width = ArrayStorageWidth(port.name, port.width);
    RecordSignal(port.name, width, port.is_signed, mod);
    if (port.num_unpacked_dims > 0) unpacked_arrays_.insert(port.name);
    MapPortBits(port, width, aig);
  }
  for (const auto& var : mod->variables) {
    if (signal_widths_.count(var.name)) continue;
    RecordArrayShape(var.name, var.width, var.num_unpacked_dims,
                     var.unpacked_dims);
    RecordSignal(var.name, ArrayStorageWidth(var.name, var.width),
                 var.is_signed, mod);
    if (var.unpacked_size > 0 || !var.unpacked_dim_sizes.empty()) {
      unpacked_arrays_.insert(var.name);
    }
  }
  for (const auto& net : mod->nets) {
    if (signal_widths_.count(net.name)) continue;
    RecordSignal(net.name, net.width, net.is_signed, mod);
  }
}

void SynthLower::SetSignalBit(std::string_view name, uint32_t bit,
                              uint32_t lit) {
  auto it = signal_bits_.find(name);
  if (it == signal_bits_.end()) return;
  if (bit < it->second.size()) {
    it->second[bit] = lit;
  }
}

uint32_t SynthLower::GetSignalBit(std::string_view name, uint32_t bit) {
  auto it = signal_bits_.find(name);
  if (it == signal_bits_.end()) return AigGraph::kConstFalse;
  if (bit >= it->second.size()) return AigGraph::kConstFalse;
  return it->second[bit];
}

uint32_t SynthLower::SignalWidth(std::string_view name) {
  auto it = signal_widths_.find(name);
  if (it == signal_widths_.end()) return 1;
  return it->second;
}

bool SynthLower::IsSignedSignal(std::string_view name) {
  auto it = signal_signed_.find(name);
  return it != signal_signed_.end() && it->second;
}

// True for the operators §11.8.1 rules unsigned whatever their operands are.
// The subclause names the six §11.4.9 reduction operators itself: "Comparison
// and reduction operator results are unsigned, regardless of the operands".
// §11.4.7 states the result of the logical negation `!` as `1'b0` or `1'b1`,
// and §11.8.1 rules a based number unsigned.
static bool IsUnsignedResultUnaryOp(TokenKind op) {
  switch (op) {
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
    case TokenKind::kBang:
      return true;
    default:
      return false;
  }
}

// True for the four §11.4.7 logical operators. §11.4.7 states the result of
// each as `1'b1`, `1'b0` or `1'bx`, and §11.8.1 rules a based number unsigned,
// so the type of neither operand reaches the result.
static bool IsLogicalOp(TokenKind op) {
  switch (op) {
    case TokenKind::kAmpAmp:
    case TokenKind::kPipePipe:
    case TokenKind::kArrow:
    case TokenKind::kLtDashGt:
      return true;
    default:
      return false;
  }
}

bool SynthLower::IsSignedExpr(const Expr* expr) {
  // §11.8.1 rules the type of an expression off its operands, so an operator
  // that carries a type out is answered from the operands it counts. §11.8.1
  // also rules that "The sign and size of any self-determined operand are
  // determined by the operand itself and independent of the remainder of the
  // expression", so a self-determined operand is not one of them.
  if (!expr) return false;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      return IsSignedSignal(expr->text);
    case ExprKind::kIntegerLiteral:
      return IsSignedLiteral(expr->text);
    case ExprKind::kUnary:
      if (IsUnsignedResultUnaryOp(expr->op)) return false;
      return IsSignedExpr(expr->lhs);
    case ExprKind::kBinary:
      if (IsCompareOp(expr->op) || IsLogicalOp(expr->op)) return false;
      // §11.4.10 rules that a shift's right operand "has no effect on the
      // signedness of the result", and §11.6.1 Table 11-21 marks that operand
      // self-determined, so the left operand alone answers for a shift.
      if (IsShiftOp(expr->op)) return IsSignedExpr(expr->lhs);
      // §11.8.1: "If all operands are signed, the result will be signed,
      // regardless of operator", and "If any operand is unsigned, the result
      // is unsigned, regardless of the operator".
      return IsSignedExpr(expr->lhs) && IsSignedExpr(expr->rhs);
    case ExprKind::kTernary:
      // §11.6.1 Table 11-21 marks the condition of `i ? j : k`
      // self-determined, so the two arms are the operands §11.8.1 counts.
      return IsSignedExpr(expr->true_expr) && IsSignedExpr(expr->false_expr);
    default:
      // §11.8.1 rules concatenation results, bit-select results and part-select
      // results unsigned regardless of their operands, and §5.7.1 states the
      // unsized single-bit values `'0`, `'1`, `'x` and `'z` unsigned.
      return false;
  }
}

uint32_t SynthLower::LowerIdentBit(std::string_view name, uint32_t bit) {
  return GetSignalBit(name, bit);
}

const PatternBits& SynthLower::LiteralBits(const Expr* expr) {
  auto it = literal_bits_.find(expr);
  if (it != literal_bits_.end()) return it->second;
  // TokenKind::kKwCase reads every digit as a value. The don't-care digits
  // §12.5.1 defines belong to a case item's pattern, and a literal standing in
  // an expression is not one.
  return literal_bits_
      .emplace(expr, ParsePatternLiteral(expr->text, TokenKind::kKwCase))
      .first->second;
}

uint32_t SynthLower::LowerLiteralBit(const Expr* expr, uint32_t bit) {
  // §5.7.1 sizes an integer literal by its size constant, "in terms of its
  // exact number of bits", which admits a literal wider than the 64 bits
  // Expr::int_val holds: `128'h1_0000_0000_0000_0000` writes bit 64, and
  // Parser::ParseIntText leaves int_val at zero for a value that overflows it.
  // The digits are therefore what answers a literal written with a base.
  const PatternBits& bits = LiteralBits(expr);
  if (bits.has_digits) {
    // §5.7.1 pads the number "to the left with zeros" above the positions its
    // digits reached.
    return PatternBitValue(bits, bit) ? AigGraph::kConstTrue
                                      : AigGraph::kConstFalse;
  }
  // A decimal literal writes no per-digit bits, so its value is the one
  // Parser::ParseIntText folded into Expr::int_val, and the positions above
  // what that holds are the zeros §5.7.1 pads with.
  if (bit >= 64) return AigGraph::kConstFalse;
  return ((expr->int_val >> bit) & 1u) != 0 ? AigGraph::kConstTrue
                                            : AigGraph::kConstFalse;
}

uint32_t SynthLower::LowerAssignRhsBit(const Expr* rhs, AigGraph& aig,
                                       uint32_t bit) {
  // §10.7: a right-hand side narrower than the assignment target is extended to
  // the target width. For a bare signed identifier, the bits beyond its own
  // width replicate its most-significant (sign) bit; unsigned identifiers and
  // all other expression forms fall through to the default zero-fill that
  // LowerExprBit already provides for out-of-range bits.
  if (rhs && rhs->kind == ExprKind::kIdentifier) {
    uint32_t rhs_width = SignalWidth(rhs->text);
    if (rhs_width > 0 && bit >= rhs_width && IsSignedSignal(rhs->text))
      return GetSignalBit(rhs->text, rhs_width - 1);
  }
  return LowerExprBit(rhs, aig, bit);
}

uint32_t FullAdderBit(AigGraph& aig, uint32_t a, uint32_t b, uint32_t& carry) {
  uint32_t half = aig.AddXor(a, b);
  uint32_t sum = aig.AddXor(half, carry);
  carry = aig.AddOr(aig.AddAnd(a, b), aig.AddAnd(half, carry));
  return sum;
}

// Build the chain again for each bit rather than keeping a memo of it.
// AigGraph::AddAnd in src/synthesizer/aig.cpp hashes each pair of literals
// through strash_ and hands back the node it already built for that pair, so
// the graph an n-bit sum lowers to holds one chain however many times this runs
// over it. Only the construction is quadratic in the operand width. A memo
// would instead be state to invalidate every time LowerIfStmt or LowerCaseStmt
// rewrites signal_bits_, because the same expression lowers to different
// literals on the two sides of a branch.
uint32_t SynthLower::LowerAddSubBit(const Expr* expr, AigGraph& aig,
                                    uint32_t bit) {
  // §11.4.3: `a - b` is `a + ~b + 1`, so subtraction is the same chain over the
  // complemented right operand with a carry of one into bit 0.
  bool subtract = expr->op == TokenKind::kMinus;
  uint32_t carry = subtract ? AigGraph::kConstTrue : AigGraph::kConstFalse;
  uint32_t sum = AigGraph::kConstFalse;
  for (uint32_t b = 0; b <= bit; ++b) {
    uint32_t l = LowerExprBit(expr->lhs, aig, b);
    uint32_t r = LowerExprBit(expr->rhs, aig, b);
    sum = FullAdderBit(aig, l, subtract ? aig.AddNot(r) : r, carry);
  }
  return sum;
}

bool SynthLower::ReportArithIfUnlowered(const Expr* expr) {
  NonSynthRule rule = NonSynthArithRule(expr->op);
  if (rule.message.empty()) return false;
  ReportExprUnlowered(expr, rule.message, Subclause(rule.subclause));
  return true;
}

uint32_t SynthLower::LowerBinaryBit(const Expr* expr, AigGraph& aig,
                                    uint32_t bit) {
  if (expr->op == TokenKind::kPlus || expr->op == TokenKind::kMinus) {
    return LowerAddSubBit(expr, aig, bit);
  }
  if (IsCompareOp(expr->op)) return LowerCompareBit(expr, aig, bit);
  if (IsShiftOp(expr->op)) return LowerShiftBit(expr, aig, bit);
  if (ReportArithIfUnlowered(expr)) return AigGraph::kConstFalse;
  uint32_t l = LowerExprBit(expr->lhs, aig, bit);
  uint32_t r = LowerExprBit(expr->rhs, aig, bit);
  switch (expr->op) {
    case TokenKind::kAmp:
      return aig.AddAnd(l, r);
    case TokenKind::kPipe:
      return aig.AddOr(l, r);
    case TokenKind::kCaret:
      return aig.AddXor(l, r);
    case TokenKind::kTildeAmp:
      return aig.AddNot(aig.AddAnd(l, r));
    case TokenKind::kTildePipe:
      return aig.AddNot(aig.AddOr(l, r));
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return aig.AddNot(aig.AddXor(l, r));
    case TokenKind::kAmpAmp:
      if (bit > 0) return AigGraph::kConstFalse;
      return aig.AddAnd(l, r);
    case TokenKind::kPipePipe:
      if (bit > 0) return AigGraph::kConstFalse;
      return aig.AddOr(l, r);
    case TokenKind::kArrow:
      if (bit > 0) return AigGraph::kConstFalse;
      return aig.AddOr(aig.AddNot(l), r);
    case TokenKind::kLtDashGt:
      if (bit > 0) return AigGraph::kConstFalse;
      return aig.AddNot(aig.AddXor(l, r));
    default:
      return AigGraph::kConstFalse;
  }
}

uint32_t SynthLower::LowerExprBit(const Expr* expr, AigGraph& aig,
                                  uint32_t bit) {
  if (!expr) return AigGraph::kConstFalse;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      return LowerIdentBit(expr->text, bit);
    case ExprKind::kIntegerLiteral:
      return LowerLiteralBit(expr, bit);
    case ExprKind::kUnbasedUnsizedLiteral:
      // §5.7.1 rules that the unsized unsigned single-bit values `'0`, `'1`,
      // `'x` and `'z` set "all bits of the unsized value" to the bit specified,
      // so which position is asked for does not change the answer.
      // Parser::MakeLiteral records `'1` as every bit of Expr::int_val set.
      return expr->int_val != 0 ? AigGraph::kConstTrue : AigGraph::kConstFalse;
    case ExprKind::kUnary:
      return LowerUnaryBit(expr, aig, bit);
    case ExprKind::kBinary:
      return LowerBinaryBit(expr, aig, bit);
    case ExprKind::kSelect:
      return LowerSelectBit(expr, aig, bit);
    case ExprKind::kConcatenation:
      return LowerConcatBit(expr, aig, bit);
    case ExprKind::kReplicate:
      return LowerReplicateBit(expr, aig, bit);
    case ExprKind::kTernary: {
      uint32_t sel = LowerExprBit(expr->condition, aig, 0);
      uint32_t t = LowerExprBit(expr->true_expr, aig, bit);
      uint32_t f = LowerExprBit(expr->false_expr, aig, bit);
      return aig.AddMux(sel, t, f);
    }
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kSystemCall:
    case ExprKind::kMemberAccess:
    case ExprKind::kCall:
    case ExprKind::kAssignmentPattern:
    case ExprKind::kCast:
    case ExprKind::kTypeRef:
    case ExprKind::kPostfixUnary:
    case ExprKind::kInside:
    case ExprKind::kStreamingConcat:
    case ExprKind::kMinTypMax:
    case ExprKind::kTagged:
      break;
  }
  // Every kind is named above, so a kind added to ExprKind in
  // src/parser/ast_expr.h is a compile error here rather than an expression
  // silently answering constant zero. That is the property whose absence let
  // these fourteen through.
  NonSynthRule rule = expr->kind == ExprKind::kMemberAccess
                          ? DottedNameRule(expr)
                          : NonSynthExprRule(expr->kind);
  ReportExprUnlowered(expr, rule.message, Subclause(rule.subclause));
  return AigGraph::kConstFalse;
}

void SynthLower::LowerContAssign(const RtlirContAssign& assign, AigGraph& aig) {
  if (!assign.lhs || !assign.rhs) return;
  SetGenScope(assign.gen_block_consts);
  if (assign.lhs->kind == ExprKind::kSelect) {
    LowerSelectTarget(assign.lhs, assign.rhs, aig);
    return;
  }
  if (assign.lhs->kind != ExprKind::kIdentifier) {
    ReportUnloweredTarget(assign.lhs);
    return;
  }
  std::string_view name = assign.lhs->text;
  uint32_t width = assign.width > 0 ? assign.width : SignalWidth(name);
  // §11.8.2: the size of the target propagates back down to the
  // context-determined operands of the right-hand side. It is cleared again
  // below so that an expression lowered outside an assignment, such as the
  // condition of an if statement, is left self-determined.
  propagated_width_ = width;
  // §11.8.2 propagates the type of the expression down with its size. §11.8.1
  // rules that the type "does not depend on the left-hand side (if any)", so
  // this reads the right-hand side rather than the target.
  propagated_signed_ = IsSignedExpr(assign.rhs);
  for (uint32_t b = 0; b < width; ++b) {
    SetSignalBit(name, b, LowerAssignRhsBit(assign.rhs, aig, b));
  }
  propagated_width_ = 0;
  propagated_signed_ = false;
}

void SynthLower::LowerIfStmt(const Stmt* stmt, AigGraph& aig) {
  auto saved = signal_bits_;
  LowerStmt(stmt->then_branch, aig);
  auto then_bits = signal_bits_;

  signal_bits_ = saved;
  if (stmt->else_branch) {
    LowerStmt(stmt->else_branch, aig);
  }
  auto else_bits = signal_bits_;

  uint32_t sel = LowerExprBit(stmt->condition, aig, 0);
  for (auto& [name, bits] : signal_bits_) {
    auto then_it = then_bits.find(name);
    if (then_it == then_bits.end()) continue;
    auto& else_vec = else_bits[name];
    for (uint32_t b = 0; b < bits.size(); ++b) {
      uint32_t t = then_it->second[b];
      uint32_t e = else_vec[b];
      if (t != e) bits[b] = aig.AddMux(sel, t, e);
    }
  }
}

void SynthLower::LowerCaseStmt(const Stmt* stmt, AigGraph& aig) {
  const CaseItem* default_item = nullptr;
  for (const auto& ci : stmt->case_items) {
    if (ci.is_default) {
      default_item = &ci;
      break;
    }
  }

  auto base_bits = signal_bits_;
  if (default_item && default_item->body) {
    LowerStmt(default_item->body, aig);
  }
  auto result_bits = signal_bits_;

  uint32_t sel_width = SignalWidth(stmt->condition->text);
  // §12.5.4 rules that "the inside operator uses asymmetric wildcard matching
  // (see 11.4.6)" and that each case_item_expression is its right operand.
  // §11.4.6 makes both the x and the z of that operand wildcards, which is the
  // pair TokenKind::kKwCasex asks BuildPatternMatch to read out of an item's
  // own digits. The asymmetry needs nothing further: the digits are read from
  // the item, and a selector arrives as AIG literals carrying no x or z at all.
  TokenKind item_kind =
      stmt->case_inside ? TokenKind::kKwCasex : stmt->case_kind;
  for (const auto& ci : stmt->case_items) {
    if (ci.is_default) continue;
    signal_bits_ = base_bits;
    LowerStmt(ci.body, aig);
    auto case_bits = signal_bits_;

    uint32_t match = AigGraph::kConstFalse;
    LowerCtx ctx{aig, *this};
    for (const auto* pat : ci.patterns) {
      match = aig.AddOr(match, BuildPatternMatch(stmt->condition, pat, ctx,
                                                 sel_width, item_kind));
    }
    MuxCaseBits(result_bits, case_bits, match, aig);
  }
  signal_bits_ = result_bits;
}

// True for a statement kind that leaves the graph alone because there is
// nothing in it to lower, as opposed to one this synthesizer has not been
// taught to lower. A null statement (§9.4) describes no behaviour at all, and
// a declaration inside a block (§9.3.1) introduces a name whose storage
// MapPorts has already reserved from the module's variable list.
static bool LowersToNothing(StmtKind kind) {
  switch (kind) {
    case StmtKind::kNull:
    case StmtKind::kVarDecl:
    case StmtKind::kBlockItemDecl:
      return true;
    default:
      return false;
  }
}

// Lower `y++`, `++y`, `y--` and `--y` as the blocking assignment §11.4.2 rules
// each one behaves as, and answer false for anything else so that LowerStmt
// reports the statement rather than passing over it. The new value is built
// over the operand's own width by a chain of FullAdderBit stages carrying one
// into bit 0. `++` adds the constant zero to the operand, which makes the sum
// `y + 1`. `--` adds the complement of the constant one, whose bit 0 is false
// and whose every higher bit is true, which makes the sum `y + ~1 + 1`, and
// that is `y - 1`. The addend is the one place the two directions differ.
//
// The postfix and prefix spellings lower alike here. They yield different
// values as expressions, the operand's old value and its new one, but they
// assign the same value, and an expression statement (§9.2) yields its value to
// nobody.
//
// An operand that is not a whole variable, such as `y[0]++`, answers false,
// because the chain reads and writes whole signals through GetSignalBit and
// SetSignalBit.
bool SynthLower::LowerIncDecStmt(const Expr* expr, AigGraph& aig) {
  if (expr->op != TokenKind::kPlusPlus && expr->op != TokenKind::kMinusMinus) {
    return false;
  }
  if (expr->lhs->kind != ExprKind::kIdentifier) return false;
  std::string_view name = expr->lhs->text;
  bool down = expr->op == TokenKind::kMinusMinus;
  uint32_t carry = AigGraph::kConstTrue;
  for (uint32_t b = 0; b < SignalWidth(name); ++b) {
    uint32_t addend =
        (down && b > 0) ? AigGraph::kConstTrue : AigGraph::kConstFalse;
    SetSignalBit(name, b,
                 FullAdderBit(aig, GetSignalBit(name, b), addend, carry));
  }
  return true;
}

void SynthLower::LowerStmt(const Stmt* stmt, AigGraph& aig) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlock) {
    for (const auto* s : stmt->stmts) {
      LowerStmt(s, aig);
    }
    return;
  }
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    LowerAssignStmt(stmt, aig);
    return;
  }
  if (stmt->kind == StmtKind::kIf) {
    LowerIfStmt(stmt, aig);
    return;
  }
  if (stmt->kind == StmtKind::kCase) {
    LowerCaseStmt(stmt, aig);
    return;
  }
  if (stmt->kind == StmtKind::kExprStmt && LowerIncDecStmt(stmt->expr, aig)) {
    return;
  }
  if (LowersToNothing(stmt->kind)) return;
  // Everything else is a statement CheckStmtSynthesizable let through and this
  // function has no lowering for, which used to mean the statement and every
  // statement nested in it left no trace in the graph while the run reported
  // success. Say so instead. No subclause of IEEE 1800-2023 states this: it is
  // a limit of this synthesizer rather than a rule the design broke, and the
  // location is what tells the reader which statement went missing.
  lowering_incomplete_ = true;
  diag_.Error(stmt->range.start,
              "statement has no lowering in the synthesizer and would be "
              "dropped from the netlist",
              Subclause::None());
}

void SynthLower::LowerAssignStmt(const Stmt* stmt, AigGraph& aig) {
  if (!stmt->lhs || !stmt->rhs) return;
  if (stmt->lhs->kind == ExprKind::kSelect) {
    LowerSelectTarget(stmt->lhs, stmt->rhs, aig);
    return;
  }
  if (stmt->lhs->kind != ExprKind::kIdentifier) {
    ReportUnloweredTarget(stmt->lhs);
    return;
  }
  uint32_t w = SignalWidth(stmt->lhs->text);
  // §11.8.2, as in SynthLower::LowerContAssign: the target propagates its size
  // down to the context-determined operands of the right-hand side.
  propagated_width_ = w;
  propagated_signed_ = IsSignedExpr(stmt->rhs);
  for (uint32_t b = 0; b < w; ++b) {
    SetSignalBit(stmt->lhs->text, b, LowerAssignRhsBit(stmt->rhs, aig, b));
  }
  propagated_width_ = 0;
  propagated_signed_ = false;
}

void SynthLower::MuxCaseBits(
    std::unordered_map<std::string_view, std::vector<uint32_t>>& result,
    const std::unordered_map<std::string_view, std::vector<uint32_t>>& src,
    uint32_t match, AigGraph& aig) {
  for (auto& [name, bits] : result) {
    auto it = src.find(name);
    if (it == src.end()) continue;
    for (uint32_t b = 0; b < bits.size(); ++b) {
      if (it->second[b] != bits[b]) {
        bits[b] = aig.AddMux(match, it->second[b], bits[b]);
      }
    }
  }
}

void SynthLower::LowerAlwaysComb(const RtlirProcess& proc, AigGraph& aig) {
  LowerStmt(proc.body, aig);
}

void SynthLower::CreateLatches(
    const std::unordered_map<std::string_view, std::vector<uint32_t>>& saved,
    AigGraph& aig) {
  for (auto& [name, bits] : signal_bits_) {
    auto saved_it = saved.find(name);
    if (saved_it == saved.end()) continue;
    for (uint32_t b = 0; b < bits.size(); ++b) {
      if (bits[b] != saved_it->second[b]) {
        bits[b] = aig.AddLatch(bits[b]);
      }
    }
  }
}

void SynthLower::LowerAlwaysFF(const RtlirProcess& proc, AigGraph& aig) {
  auto saved = signal_bits_;
  LowerStmt(proc.body, aig);
  CreateLatches(saved, aig);
}

void SynthLower::LowerAlwaysLatch(const RtlirProcess& proc, AigGraph& aig) {
  auto saved = signal_bits_;
  LowerStmt(proc.body, aig);
  CreateLatches(saved, aig);
}

void SynthLower::RegisterOutputs(AigGraph& aig) {
  for (const auto& [name, width] : output_ports_) {
    for (uint32_t b = 0; b < width; ++b) {
      aig.AddOutput(GetSignalBit(name, b));
    }
  }
}

AigGraph* SynthLower::Lower(const RtlirModule* mod) {
  if (!mod) return nullptr;
  if (!CheckSynthesizable(mod)) return nullptr;

  auto* aig = arena_.Create<AigGraph>();
  ResetForModule(mod);
  MapPorts(mod, *aig);

  for (const auto& assign : mod->assigns) {
    LowerContAssign(assign, *aig);
  }

  for (const auto& proc : mod->processes) {
    SetGenScope(proc.gen_block_consts);
    switch (proc.kind) {
      case RtlirProcessKind::kAlwaysComb:
        LowerAlwaysComb(proc, *aig);
        break;
      case RtlirProcessKind::kAlways:
        if (proc.is_star_sensitivity) {
          LowerAlwaysComb(proc, *aig);
        } else if (!SensitivityHasEdge(proc) && SensitivityHasIff(proc)) {
          // §9.4.2.3: level-sensitive event control gated by `iff` → latch.
          LowerAlwaysLatch(proc, *aig);
        }
        break;
      case RtlirProcessKind::kAlwaysFF:
        LowerAlwaysFF(proc, *aig);
        break;
      case RtlirProcessKind::kAlwaysLatch:
        LowerAlwaysLatch(proc, *aig);
        break;
      default:
        break;
    }
  }

  RegisterOutputs(*aig);
  // A graph built over a statement that was passed over describes something
  // other than the module, so answer with nothing rather than with that.
  if (lowering_incomplete_) return nullptr;
  return aig;
}

}  // namespace delta
