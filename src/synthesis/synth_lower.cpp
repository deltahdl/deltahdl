#include "synthesis/synth_lower.h"

#include <string>

namespace delta {

SynthLower::SynthLower(Arena& arena, DiagEngine& diag)
    : arena_(arena), diag_(diag) {}

// =============================================================================
// Synthesizability checker
// =============================================================================

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
    if (proc.kind == RtlirProcessKind::kInitial) {
      diag_.Error(SourceLoc{}, "'initial' block is not synthesizable");
      return false;
    }
    if (proc.kind == RtlirProcessKind::kFinal) {
      diag_.Error(SourceLoc{}, "'final' block is not synthesizable");
      return false;
    }
    if (!CheckStmtSynthesizable(proc.body)) return false;
  }
  return true;
}

// =============================================================================
// Port I/O mapping
// =============================================================================

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

// =============================================================================
// Signal bit access
// =============================================================================

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

// =============================================================================
// Expression lowering (per-bit)
// =============================================================================

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

// =============================================================================
// Continuous assignment lowering
// =============================================================================

void SynthLower::LowerContAssign(const RtlirContAssign& assign, AigGraph& aig) {
  if (!assign.lhs || !assign.rhs) return;
  if (assign.lhs->kind != ExprKind::kIdentifier) return;
  std::string_view name = assign.lhs->text;
  uint32_t width = assign.width > 0 ? assign.width : SignalWidth(name);
  for (uint32_t b = 0; b < width; ++b) {
    SetSignalBit(name, b, LowerExprBit(assign.rhs, aig, b));
  }
}

// =============================================================================
// Statement lowering for combinational processes
// =============================================================================

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

static uint32_t BuildPatternMatch(const Expr* sel_expr, const Expr* pat,
                                  AigGraph& aig, SynthLower& synth,
                                  uint32_t sel_width) {
  uint32_t eq = AigGraph::kConstTrue;
  for (uint32_t b = 0; b < sel_width; ++b) {
    uint32_t sb = synth.LowerExprBit(sel_expr, aig, b);
    uint32_t pb = synth.LowerExprBit(pat, aig, b);
    eq = aig.AddAnd(eq, aig.AddNot(aig.AddXor(sb, pb)));
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
    for (const auto* pat : ci.patterns) {
      match = aig.AddOr(match, BuildPatternMatch(stmt->condition, pat, aig,
                                                 *this, sel_width));
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

// =============================================================================
// always_comb lowering
// =============================================================================

void SynthLower::LowerAlwaysComb(const RtlirProcess& proc, AigGraph& aig) {
  LowerStmt(proc.body, aig);
}

// =============================================================================
// always_ff / always_latch lowering
// =============================================================================

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

// =============================================================================
// Output registration
// =============================================================================

void SynthLower::RegisterOutputs(AigGraph& aig) {
  for (const auto& [name, width] : output_ports_) {
    for (uint32_t b = 0; b < width; ++b) {
      aig.AddOutput(GetSignalBit(name, b));
    }
  }
}

// =============================================================================
// Top-level Lower
// =============================================================================

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
