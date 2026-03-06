#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

// Defined in elaborator.cpp.
uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod);

/// Build a binary expression tree from left-folding the given operand over
/// all inputs with the given operator.
static Expr* BuildBinaryChain(Arena& arena, TokenKind op,
                              const std::vector<Expr*>& inputs) {
  Expr* result = inputs[0];
  for (size_t i = 1; i < inputs.size(); ++i) {
    auto* bin = arena.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = op;
    bin->lhs = result;
    bin->rhs = inputs[i];
    result = bin;
  }
  return result;
}

/// Wrap an expression in a unary NOT (~).
static Expr* WrapInvert(Arena& arena, Expr* inner) {
  auto* inv = arena.Create<Expr>();
  inv->kind = ExprKind::kUnary;
  inv->op = TokenKind::kTilde;
  inv->lhs = inner;
  return inv;
}

/// Create an integer literal expression with the given value.
static Expr* MakeIntLiteral(Arena& arena, uint64_t val) {
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = val;
  return lit;
}

/// Build the RHS expression for an N-input gate (and/nand/or/nor/xor/xnor).
static Expr* BuildNInputGateExpr(Arena& arena, GateKind kind,
                                 const std::vector<Expr*>& terminals) {
  // terminals[0] = output, terminals[1..n-1] = inputs.
  std::vector<Expr*> inputs(terminals.begin() + 1, terminals.end());
  TokenKind op = TokenKind::kAmp;
  bool invert = false;
  switch (kind) {
    case GateKind::kAnd:
      op = TokenKind::kAmp;
      break;
    case GateKind::kNand:
      op = TokenKind::kAmp;
      invert = true;
      break;
    case GateKind::kOr:
      op = TokenKind::kPipe;
      break;
    case GateKind::kNor:
      op = TokenKind::kPipe;
      invert = true;
      break;
    case GateKind::kXor:
      op = TokenKind::kCaret;
      break;
    case GateKind::kXnor:
      op = TokenKind::kCaret;
      invert = true;
      break;
    default:
      break;
  }
  auto* chain = BuildBinaryChain(arena, op, inputs);
  return invert ? WrapInvert(arena, chain) : chain;
}

/// Build RHS for buf/not/bufif/notif/pull gates.
static Expr* BuildOutputGateExpr(Arena& arena, GateKind kind,
                                 const std::vector<Expr*>& terminals) {
  switch (kind) {
    case GateKind::kBuf:
      return (terminals.size() >= 2) ? terminals.back() : nullptr;
    case GateKind::kNot:
      return (terminals.size() >= 2) ? WrapInvert(arena, terminals.back())
                                     : nullptr;
    case GateKind::kPullup:
      return MakeIntLiteral(arena, 1);
    case GateKind::kPulldown:
      return MakeIntLiteral(arena, 0);
    default:
      return nullptr;
  }
}

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.empty()) return;

  Expr* rhs = nullptr;
  switch (kind) {
    case GateKind::kAnd:
    case GateKind::kNand:
    case GateKind::kOr:
    case GateKind::kNor:
    case GateKind::kXor:
    case GateKind::kXnor:
      rhs = BuildNInputGateExpr(arena, kind, terms);
      break;
    default:
      rhs = BuildOutputGateExpr(arena, kind, terms);
      break;
  }

  if (!rhs) return;

  RtlirContAssign ca;
  ca.lhs = terms[0];
  ca.rhs = rhs;
  ca.width = LookupLhsWidth(ca.lhs, mod);
  mod->assigns.push_back(ca);
}

}  // namespace delta
