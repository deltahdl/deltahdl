#include <format>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

static const RtlirNet* FindNetByName(std::string_view name,
                                     const RtlirModule* mod) {
  for (const auto& n : mod->nets) {
    if (n.name == name) return &n;
  }
  return nullptr;
}

// §28.8: Resolve the underlying net referenced by a bidirectional terminal
// expression. Returns nullptr when the terminal does not reduce to a single
// net (e.g. concatenation, variable, or unrecognised form).
static const RtlirNet* TerminalNet(const Expr* term, const RtlirModule* mod) {
  if (!term) return nullptr;
  if (term->kind == ExprKind::kIdentifier)
    return FindNetByName(term->text, mod);
  if (term->kind == ExprKind::kSelect && term->base &&
      term->base->kind == ExprKind::kIdentifier)
    return FindNetByName(term->base->text, mod);
  return nullptr;
}

// §28.8: True when `term` is either a scalar net identifier (width 1) or a
// single-bit select on a net identifier — the only forms permitted on the
// bidirectional terminals of resistive (rtran/rtranif*) switches.
static bool IsScalarNetOrBitSelect(const Expr* term, const RtlirModule* mod) {
  if (!term) return false;
  if (term->kind == ExprKind::kIdentifier) {
    auto* net = FindNetByName(term->text, mod);
    return net != nullptr && net->width == 1;
  }
  if (term->kind == ExprKind::kSelect) {
    if (!term->base || term->base->kind != ExprKind::kIdentifier) return false;
    if (term->is_part_select_plus || term->is_part_select_minus) return false;
    if (term->index_end != nullptr) return false;
    if (term->index == nullptr) return false;
    return FindNetByName(term->base->text, mod) != nullptr;
  }
  return false;
}

static const RtlirVariable* FindVariableByName(std::string_view name,
                                               const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return &v;
  }
  return nullptr;
}

// §28.8: Reports the disqualifying type kind when the control terminal
// directly references a variable whose type cannot serve as a control input
// (real, string, chandle, event). Returns nullptr for nets, 4-state and
// 2-state variables, and for terminals that are not a bare identifier — those
// cases are either explicitly permitted or fall outside this single-signal
// rule (an arbitrary expression's type is checked elsewhere).
static const char* DisallowedControlVariableKind(const Expr* term,
                                                 const RtlirModule* mod) {
  if (!term || term->kind != ExprKind::kIdentifier) return nullptr;
  auto* var = FindVariableByName(term->text, mod);
  if (!var) return nullptr;
  if (var->is_real) return "real";
  if (var->is_string) return "string";
  if (var->is_chandle) return "chandle";
  if (var->is_event) return "event";
  return nullptr;
}

void ValidateBidirectionalSwitchConnections(const ModuleItem* item,
                                            const RtlirModule* mod,
                                            DiagEngine& diag) {
  if (!item || item->kind != ModuleItemKind::kGateInst) return;
  auto kind = item->gate_kind;
  bool is_bidir = (kind == GateKind::kTran || kind == GateKind::kRtran ||
                   kind == GateKind::kTranif0 || kind == GateKind::kTranif1 ||
                   kind == GateKind::kRtranif0 || kind == GateKind::kRtranif1);
  if (!is_bidir) return;
  const auto& terms = item->gate_terminals;
  if (terms.size() < 2) return;

  bool is_resistive = (kind == GateKind::kRtran ||
                       kind == GateKind::kRtranif0 ||
                       kind == GateKind::kRtranif1);
  if (is_resistive) {
    for (size_t i = 0; i < 2; ++i) {
      // §28.8: tran/tranif* get the "may also ... user-defined net types"
      // carve-out; the resistive variants do not, so reject UDNT terminals
      // before the scalar-net check to give a clearer diagnostic than
      // "must be a scalar net" for a net that is in fact scalar.
      auto* net = TerminalNet(terms[i], mod);
      if (net && net->is_user_nettype) {
        diag.Error(item->loc,
                   "resistive bidirectional pass switch terminal cannot "
                   "connect to a user-defined net type");
        continue;
      }
      if (!IsScalarNetOrBitSelect(terms[i], mod)) {
        diag.Error(item->loc,
                   "resistive bidirectional pass switch terminal must be a "
                   "scalar net or a bit-select of a vector net");
      }
    }
  }

  bool has_control = (kind == GateKind::kTranif0 ||
                      kind == GateKind::kTranif1 ||
                      kind == GateKind::kRtranif0 ||
                      kind == GateKind::kRtranif1);
  if (has_control && terms.size() >= 3) {
    if (auto* bad = DisallowedControlVariableKind(terms[2], mod)) {
      diag.Error(item->loc,
                 std::format("control input of pass-enable switch cannot be "
                             "of type '{}'; expected a 4-state net, 4-state "
                             "variable, or 2-state variable",
                             bad));
    }
  }

  auto* n0 = TerminalNet(terms[0], mod);
  auto* n1 = TerminalNet(terms[1], mod);
  if (!n0 || !n1) return;
  if (n0->is_user_nettype != n1->is_user_nettype) {
    diag.Error(item->loc,
               "bidirectional pass switch cannot connect a user-defined "
               "nettype to a built-in net");
    return;
  }
  if (n0->is_user_nettype && n1->is_user_nettype &&
      n0->nettype_name != n1->nettype_name) {
    diag.Error(item->loc,
               std::format("bidirectional pass switch cannot connect "
                           "different user-defined nettypes ('{}' and '{}')",
                           n0->nettype_name, n1->nettype_name));
  }
}

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

// §28.16: Gate primitives lower to continuous assignments; the parsed
// `#(d1, d2, d3)` on the instance must ride along to the simulator so
// Table 28-9 selection and the 1/2/3-delay rules apply to the driven net.
static void ApplyGateDelays(RtlirContAssign& ca, const ModuleItem* item) {
  ca.delay = item->gate_delay;
  ca.delay_fall = item->gate_delay_fall;
  ca.delay_decay = item->gate_delay_decay;
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
      ApplyGateDelays(ca, item);
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
    ApplyGateDelays(ca, item);
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
    // §28.13 covers nmos and pmos only; rnmos/rpmos are resistive (§28.14).
    ca.from_nonresistive_switch =
        (kind == GateKind::kNmos || kind == GateKind::kPmos);
    ca.from_resistive_switch =
        (kind == GateKind::kRnmos || kind == GateKind::kRpmos);
    if (ca.from_nonresistive_switch || ca.from_resistive_switch) {
      ca.data_input = data;
    }
    ApplyGateDelays(ca, item);
    mod->assigns.push_back(ca);
    return;
  }

  // §28.10: pullup places logic 1 on its net; pulldown places logic 0.
  // When no strength is specified these sources drive at pull strength.
  // For pullup, only the strength1 side is meaningful — any strength0 is
  // ignored (and vice versa for pulldown) because these sources only ever
  // drive a single logic level. Delay specifications are not permitted and
  // are already rejected during parsing.
  if (kind == GateKind::kPullup || kind == GateKind::kPulldown) {
    if (terms.size() != 1) return;
    bool is_up = (kind == GateKind::kPullup);
    uint8_t driving = is_up ? item->drive_strength1 : item->drive_strength0;
    if (driving == 0) driving = 3;  // pull
    RtlirContAssign ca;
    ca.lhs = terms[0];
    ca.rhs = MakeIntLiteral(arena, is_up ? 1 : 0);
    ca.width = LookupLhsWidth(ca.lhs, mod);
    ca.drive_strength0 = is_up ? 0 : driving;
    ca.drive_strength1 = is_up ? driving : 0;
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
    // §28.13: cmos is nonresistive; rcmos is resistive (§28.14).
    ca.from_nonresistive_switch = (kind == GateKind::kCmos);
    ca.from_resistive_switch = (kind == GateKind::kRcmos);
    if (ca.from_nonresistive_switch || ca.from_resistive_switch) {
      ca.data_input = data;
    }
    ApplyGateDelays(ca, item);
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
  ApplyGateDelays(ca, item);
  mod->assigns.push_back(ca);
}

}  // namespace delta
