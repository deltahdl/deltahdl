#include "common/arena.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

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

/// Create an unbased-unsized high-Z literal ('z).
static Expr* MakeHighZ(Arena& arena) {
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kUnbasedUnsizedLiteral;
  lit->text = "'z";
  return lit;
}

/// Build a ternary (cond ? t : f) expression.
static Expr* MakeTernary(Arena& arena, Expr* cond, Expr* t, Expr* f) {
  auto* tern = arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = cond;
  tern->true_expr = t;
  tern->false_expr = f;
  return tern;
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

/// Build RHS for bufif/notif/pull gates (all single-output).
static Expr* BuildOutputGateExpr(Arena& arena, GateKind kind,
                                 const std::vector<Expr*>& terminals) {
  switch (kind) {
    case GateKind::kPullup:
      return MakeIntLiteral(arena, 1);
    case GateKind::kPulldown:
      return MakeIntLiteral(arena, 0);
    default:
      return (terminals.size() >= 2) ? terminals.back() : nullptr;
  }
}

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.empty()) return;

  // §28.5: buf and not have one input (last terminal) and one or more
  // outputs (all preceding terminals); emit one continuous assign per
  // output.
  if (kind == GateKind::kBuf || kind == GateKind::kNot) {
    if (terms.size() < 2) return;
    auto* input = terms.back();
    for (size_t i = 0; i + 1 < terms.size(); ++i) {
      Expr* rhs =
          (kind == GateKind::kNot) ? WrapInvert(arena, input) : input;
      RtlirContAssign ca;
      ca.lhs = terms[i];
      ca.rhs = rhs;
      ca.width = LookupLhsWidth(ca.lhs, mod);
      mod->assigns.push_back(ca);
    }
    return;
  }

  // §28.6: tri-state gates take (output, data, control). When control
  // asserts the gate conducts (optionally inverting for notif); otherwise
  // the output is high-Z. Suffix 1 conducts on control==1, suffix 0 on
  // control==0.
  if (kind == GateKind::kBufif0 || kind == GateKind::kBufif1 ||
      kind == GateKind::kNotif0 || kind == GateKind::kNotif1) {
    if (terms.size() != 3) return;
    auto* data = terms[1];
    auto* ctrl = terms[2];
    bool invert =
        (kind == GateKind::kNotif0 || kind == GateKind::kNotif1);
    bool conduct_on_one =
        (kind == GateKind::kBufif1 || kind == GateKind::kNotif1);
    Expr* pass = invert ? WrapInvert(arena, data) : data;
    Expr* hi_z = MakeHighZ(arena);
    Expr* rhs = conduct_on_one ? MakeTernary(arena, ctrl, pass, hi_z)
                               : MakeTernary(arena, ctrl, hi_z, pass);
    RtlirContAssign ca;
    ca.lhs = terms[0];
    ca.rhs = rhs;
    ca.width = LookupLhsWidth(ca.lhs, mod);
    mod->assigns.push_back(ca);
    return;
  }

  // §28.8: bidirectional pass switches have no unique driven terminal, so
  // they cannot be lowered to a continuous assignment. Skip emitting any
  // driver here; switch-network resolution happens at simulation time.
  if (kind == GateKind::kTran || kind == GateKind::kRtran ||
      kind == GateKind::kTranif0 || kind == GateKind::kTranif1 ||
      kind == GateKind::kRtranif0 || kind == GateKind::kRtranif1) {
    return;
  }

  // §28.7: MOS switches take (output, data, control) and pass data through
  // only when conducting; otherwise the output is high-Z. nmos/rnmos
  // conduct on control==1; pmos/rpmos conduct on control==0. MOS switches
  // do not invert data (strength attenuation is modeled elsewhere).
  if (kind == GateKind::kNmos || kind == GateKind::kPmos ||
      kind == GateKind::kRnmos || kind == GateKind::kRpmos) {
    if (terms.size() != 3) return;
    auto* data = terms[1];
    auto* ctrl = terms[2];
    bool conduct_on_one =
        (kind == GateKind::kNmos || kind == GateKind::kRnmos);
    Expr* hi_z = MakeHighZ(arena);
    Expr* rhs = conduct_on_one ? MakeTernary(arena, ctrl, data, hi_z)
                               : MakeTernary(arena, ctrl, hi_z, data);
    RtlirContAssign ca;
    ca.lhs = terms[0];
    ca.rhs = rhs;
    ca.width = LookupLhsWidth(ca.lhs, mod);
    mod->assigns.push_back(ca);
    return;
  }

  // §28.9: cmos/rcmos are an nmos+pmos pair sharing the data input/output
  // with separate n- and p-channel controls. Terminals are (out, data,
  // ncontrol, pcontrol). The nmos half conducts on ncontrol==1; the pmos
  // half conducts on pcontrol==0. The combined output is data whenever
  // either half conducts, otherwise high-Z. Equivalently:
  //   ncontrol ? data : (pcontrol ? 'z : data)
  // Strength reduction for rcmos is handled elsewhere.
  if (kind == GateKind::kCmos || kind == GateKind::kRcmos) {
    if (terms.size() != 4) return;
    auto* data = terms[1];
    auto* nctrl = terms[2];
    auto* pctrl = terms[3];
    Expr* hi_z = MakeHighZ(arena);
    Expr* pmos_branch = MakeTernary(arena, pctrl, hi_z, data);
    Expr* rhs = MakeTernary(arena, nctrl, data, pmos_branch);
    RtlirContAssign ca;
    ca.lhs = terms[0];
    ca.rhs = rhs;
    ca.width = LookupLhsWidth(ca.lhs, mod);
    mod->assigns.push_back(ca);
    return;
  }

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
