#include "synthesizer/synth_lower.h"

#include <string>

namespace delta {

SynthLower::SynthLower(Arena& arena, DiagEngine& diag)
    : arena_(arena), diag_(diag) {}

bool SynthLower::CheckExprSynthesizable(const Expr* expr) {
  if (!expr) return true;
  if (expr->kind == ExprKind::kSystemCall) {
    diag_.Error(SourceLoc{}, "system call '" + std::string(expr->callee) +
                                 "' is not synthesizable");
    return false;
  }
  if (expr->kind == ExprKind::kUnary || expr->kind == ExprKind::kBinary) {
    return CheckExprSynthesizable(expr->lhs) &&
           CheckExprSynthesizable(expr->rhs);
  }
  if (expr->kind == ExprKind::kTernary) {
    return CheckExprSynthesizable(expr->condition) &&
           CheckExprSynthesizable(expr->true_expr) &&
           CheckExprSynthesizable(expr->false_expr);
  }
  return true;
}

static bool IsNonSynthStmt(StmtKind kind) {
  return kind == StmtKind::kDelay || kind == StmtKind::kTimingControl ||
         kind == StmtKind::kWait || kind == StmtKind::kForever ||
         kind == StmtKind::kFork || kind == StmtKind::kDisable ||
         kind == StmtKind::kEventTrigger;
}

bool SynthLower::CheckStmtSynthesizable(const Stmt* stmt) {
  if (!stmt) return true;
  if (IsNonSynthStmt(stmt->kind)) {
    diag_.Error(SourceLoc{},
                "non-synthesizable statement in synthesizable block");
    return false;
  }
  if (stmt->kind == StmtKind::kExprStmt) {
    return CheckExprSynthesizable(stmt->expr);
  }
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    return CheckExprSynthesizable(stmt->rhs);
  }
  if (stmt->kind == StmtKind::kBlock) {
    return CheckBlockStmts(stmt);
  }
  if (stmt->kind == StmtKind::kIf) {
    return CheckIfSynth(stmt);
  }
  if (stmt->kind == StmtKind::kCase) {
    return CheckCaseSynth(stmt);
  }
  return true;
}

bool SynthLower::CheckBlockStmts(const Stmt* stmt) {
  for (const auto* s : stmt->stmts) {
    if (!CheckStmtSynthesizable(s)) return false;
  }
  return true;
}

bool SynthLower::CheckIfSynth(const Stmt* stmt) {
  return CheckExprSynthesizable(stmt->condition) &&
         CheckStmtSynthesizable(stmt->then_branch) &&
         CheckStmtSynthesizable(stmt->else_branch);
}

bool SynthLower::CheckCaseSynth(const Stmt* stmt) {
  for (const auto& ci : stmt->case_items) {
    if (!CheckStmtSynthesizable(ci.body)) return false;
  }
  return true;
}

bool SynthLower::CheckSynthesizable(const RtlirModule* mod) {
  for (const auto& proc : mod->processes) {
    if (proc.kind == RtlirProcessKind::kInitial ||
        proc.kind == RtlirProcessKind::kFinal)
      continue;
    if (!CheckStmtSynthesizable(proc.body)) return false;
  }
  return true;
}

void SynthLower::MapPorts(const RtlirModule* mod, AigGraph& aig) {
  for (const auto& port : mod->ports) {
    signal_widths_[port.name] = port.width;
    auto& bits = signal_bits_[port.name];
    bits.resize(port.width, AigGraph::kConstFalse);

    if (port.direction == Direction::kInput) {
      for (uint32_t b = 0; b < port.width; ++b) {
        bits[b] = aig.AddInput();
      }
    } else if (port.direction == Direction::kOutput) {
      output_ports_.emplace_back(port.name, port.width);
    }
  }

  for (const auto& var : mod->variables) {
    if (signal_widths_.count(var.name)) continue;
    signal_widths_[var.name] = var.width;
    signal_bits_[var.name].resize(var.width, AigGraph::kConstFalse);
  }
  for (const auto& net : mod->nets) {
    if (signal_widths_.count(net.name)) continue;
    signal_widths_[net.name] = net.width;
    signal_bits_[net.name].resize(net.width, AigGraph::kConstFalse);
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

uint32_t SynthLower::LowerIdentBit(std::string_view name, uint32_t bit) {
  return GetSignalBit(name, bit);
}

uint32_t SynthLower::LowerUnaryBit(const Expr* expr, AigGraph& aig,
                                   uint32_t bit) {
  uint32_t operand = LowerExprBit(expr->lhs, aig, bit);
  if (expr->op == TokenKind::kTilde) return aig.AddNot(operand);
  if (expr->op == TokenKind::kBang) {
    if (bit > 0) return AigGraph::kConstFalse;
    return aig.AddNot(operand);
  }
  return operand;
}

uint32_t SynthLower::LowerBinaryBit(const Expr* expr, AigGraph& aig,
                                    uint32_t bit) {
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
    case ExprKind::kUnbasedUnsizedLiteral:
      return ((expr->int_val >> bit) & 1u) != 0 ? AigGraph::kConstTrue
                                                : AigGraph::kConstFalse;
    case ExprKind::kUnary:
      return LowerUnaryBit(expr, aig, bit);
    case ExprKind::kBinary:
      return LowerBinaryBit(expr, aig, bit);
    case ExprKind::kTernary: {
      uint32_t sel = LowerExprBit(expr->condition, aig, 0);
      uint32_t t = LowerExprBit(expr->true_expr, aig, bit);
      uint32_t f = LowerExprBit(expr->false_expr, aig, bit);
      return aig.AddMux(sel, t, f);
    }
    default:
      return AigGraph::kConstFalse;
  }
}

void SynthLower::LowerContAssign(const RtlirContAssign& assign, AigGraph& aig) {
  if (!assign.lhs || !assign.rhs) return;
  if (assign.lhs->kind != ExprKind::kIdentifier) return;
  std::string_view name = assign.lhs->text;
  uint32_t width = assign.width > 0 ? assign.width : SignalWidth(name);
  for (uint32_t b = 0; b < width; ++b) {
    SetSignalBit(name, b, LowerExprBit(assign.rhs, aig, b));
  }
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

struct PatternBits {
  uint64_t aval = 0;
  uint64_t dc_mask = 0;
};

static std::string StripPatternSeparators(std::string_view text) {
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_' && c != ' ' && c != '\t') buf.push_back(c);
  }
  return buf;
}

// Decimal literals carry no per-bit data, so any z/? (or x under casex) makes
// the entire pattern don't-care. Returns true if such a token was found and
// the result was set accordingly.
static bool ScanDecimalForDontCare(const std::string& buf, size_t start,
                                   TokenKind case_kind, PatternBits& result) {
  for (size_t j = start; j < buf.size(); ++j) {
    char c = buf[j];
    bool is_z = (c == 'z' || c == 'Z' || c == '?');
    bool is_x = (c == 'x' || c == 'X');
    if (is_z || (is_x && case_kind == TokenKind::kKwCasex)) {
      result.dc_mask = ~uint64_t{0};
      return true;
    }
  }
  return false;
}

// True if char c marks a don't-care digit under the given case kind. Under
// casez only z/?/Z is don't-care; otherwise x/X is don't-care too.
static bool IsDontCareDigit(char c, TokenKind case_kind) {
  bool is_z = (c == 'z' || c == 'Z' || c == '?');
  bool is_x = (c == 'x' || c == 'X');
  return (case_kind == TokenKind::kKwCasez) ? is_z : (is_z || is_x);
}

// Numeric value of a single binary/octal/hex digit character.
static uint64_t DigitCharValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return 0;
}

// Mark all bits contributed by one don't-care digit at bit_pos in the mask.
static void MarkDontCareBits(uint32_t bit_pos, int bits_per_digit,
                             PatternBits& result) {
  for (int b = 0; b < bits_per_digit && bit_pos + b < 64; ++b)
    result.dc_mask |= uint64_t{1} << (bit_pos + b);
}

// OR one decoded digit value (dv) into aval starting at bit_pos.
static void SetDigitValueBits(uint64_t dv, uint32_t bit_pos, int bits_per_digit,
                              PatternBits& result) {
  for (int b = 0; b < bits_per_digit && bit_pos + b < 64; ++b) {
    if ((dv >> b) & 1u) result.aval |= uint64_t{1} << (bit_pos + b);
  }
}

static void DecodePatternDigits(const std::string& buf, size_t i,
                                int bits_per_digit, TokenKind case_kind,
                                PatternBits& result) {
  uint32_t bit_pos = 0;
  for (size_t j = buf.size(); j > i; --j) {
    char c = buf[j - 1];
    if (IsDontCareDigit(c, case_kind)) {
      MarkDontCareBits(bit_pos, bits_per_digit, result);
    } else {
      SetDigitValueBits(DigitCharValue(c), bit_pos, bits_per_digit, result);
    }
    bit_pos += bits_per_digit;
  }
}

static PatternBits ParsePatternLiteral(std::string_view text,
                                       TokenKind case_kind) {
  PatternBits result{};
  std::string buf = StripPatternSeparators(text);
  auto tick = buf.find('\'');
  if (tick == std::string::npos) return result;

  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  if (i >= buf.size()) return result;

  int bits_per_digit = 0;
  switch (buf[i]) {
    case 'b':
    case 'B':
      bits_per_digit = 1;
      break;
    case 'o':
    case 'O':
      bits_per_digit = 3;
      break;
    case 'h':
    case 'H':
      bits_per_digit = 4;
      break;
    case 'd':
    case 'D':
      ScanDecimalForDontCare(buf, i + 1, case_kind, result);
      return result;
    default:
      return result;
  }
  ++i;

  DecodePatternDigits(buf, i, bits_per_digit, case_kind, result);
  return result;
}

// The lowering engine objects (§12.5 case lowering) threaded through the
// pattern-match family: the AIG being built and the SynthLower bit lowerer.
struct LowerCtx {
  AigGraph& aig;
  SynthLower& synth;
};

// One case-item pattern (§12.5.1 casez/casez wildcards) after decoding: the
// source literal expression plus its decoded aval/dc_mask and whether wildcard
// decoding applies at all.
struct DecodedPattern {
  const Expr* pat;
  PatternBits bits;
  bool has_dc;
};

static uint32_t PatternBitLit(const LowerCtx& ctx, const DecodedPattern& pat,
                              uint32_t b) {
  if (pat.has_dc) {
    return ((pat.bits.aval >> b) & 1u) ? AigGraph::kConstTrue
                                       : AigGraph::kConstFalse;
  }
  return ctx.synth.LowerExprBit(pat.pat, ctx.aig, b);
}

static uint32_t BuildPatternMatch(const Expr* sel_expr, const Expr* pat,
                                  const LowerCtx& ctx, uint32_t sel_width,
                                  TokenKind case_kind) {
  DecodedPattern dp{pat, PatternBits{},
                    (case_kind != TokenKind::kKwCase) &&
                        (pat->kind == ExprKind::kIntegerLiteral)};
  if (dp.has_dc) dp.bits = ParsePatternLiteral(pat->text, case_kind);

  uint32_t eq = AigGraph::kConstTrue;
  for (uint32_t b = 0; b < sel_width; ++b) {
    if (dp.has_dc && ((dp.bits.dc_mask >> b) & 1u)) continue;
    uint32_t sb = ctx.synth.LowerExprBit(sel_expr, ctx.aig, b);
    uint32_t pb = PatternBitLit(ctx, dp, b);
    eq = ctx.aig.AddAnd(eq, ctx.aig.AddNot(ctx.aig.AddXor(sb, pb)));
  }
  return eq;
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
  for (const auto& ci : stmt->case_items) {
    if (ci.is_default) continue;
    signal_bits_ = base_bits;
    LowerStmt(ci.body, aig);
    auto case_bits = signal_bits_;

    uint32_t match = AigGraph::kConstFalse;
    LowerCtx ctx{aig, *this};
    for (const auto* pat : ci.patterns) {
      match = aig.AddOr(match, BuildPatternMatch(stmt->condition, pat, ctx,
                                                 sel_width, stmt->case_kind));
    }
    MuxCaseBits(result_bits, case_bits, match, aig);
  }
  signal_bits_ = result_bits;
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
  }
}

void SynthLower::LowerAssignStmt(const Stmt* stmt, AigGraph& aig) {
  if (!stmt->lhs || !stmt->rhs) return;
  if (stmt->lhs->kind != ExprKind::kIdentifier) return;
  uint32_t w = SignalWidth(stmt->lhs->text);
  for (uint32_t b = 0; b < w; ++b) {
    SetSignalBit(stmt->lhs->text, b, LowerExprBit(stmt->rhs, aig, b));
  }
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
  signal_bits_.clear();
  signal_widths_.clear();
  output_ports_.clear();

  MapPorts(mod, *aig);

  for (const auto& assign : mod->assigns) {
    LowerContAssign(assign, *aig);
  }

  for (const auto& proc : mod->processes) {
    switch (proc.kind) {
      case RtlirProcessKind::kAlwaysComb:
        LowerAlwaysComb(proc, *aig);
        break;
      case RtlirProcessKind::kAlways:
        if (proc.is_star_sensitivity) {
          LowerAlwaysComb(proc, *aig);
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
  return aig;
}

}  // namespace delta
