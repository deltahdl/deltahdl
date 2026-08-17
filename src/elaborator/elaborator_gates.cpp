#include <algorithm>
#include <format>
#include <functional>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
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

static const RtlirNet* TerminalNet(const Expr* term, const RtlirModule* mod) {
  if (!term) return nullptr;
  if (term->kind == ExprKind::kIdentifier)
    return FindNetByName(term->text, mod);
  if (term->kind == ExprKind::kSelect && term->base &&
      term->base->kind == ExprKind::kIdentifier)
    return FindNetByName(term->base->text, mod);
  return nullptr;
}

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

static bool IsBidirectionalSwitch(GateKind kind) {
  return (kind == GateKind::kTran || kind == GateKind::kRtran ||
          kind == GateKind::kTranif0 || kind == GateKind::kTranif1 ||
          kind == GateKind::kRtranif0 || kind == GateKind::kRtranif1);
}

static bool IsResistiveBidirectionalSwitch(GateKind kind) {
  return (kind == GateKind::kRtran || kind == GateKind::kRtranif0 ||
          kind == GateKind::kRtranif1);
}

static bool IsControlBidirectionalSwitch(GateKind kind) {
  return (kind == GateKind::kTranif0 || kind == GateKind::kTranif1 ||
          kind == GateKind::kRtranif0 || kind == GateKind::kRtranif1);
}

// §6.6.2: a uwire net allows only a single driver, so it shall not be
// connected to a bidirectional terminal of a bidirectional pass switch
// (which is itself a potential driver). The first two terminals are the
// bidirectional ones for every tran/tranif variant.
static void CheckBidirUwireTerminals(const ModuleItem* item,
                                     const RtlirModule* mod, DiagEngine& diag) {
  const auto& terms = item->gate_terminals;
  for (size_t i = 0; i < 2; ++i) {
    auto* net = TerminalNet(terms[i], mod);
    if (net && net->net_type == NetType::kUwire) {
      diag.Error(item->loc,
                 "uwire net cannot connect to a bidirectional terminal of a "
                 "bidirectional pass switch",
                 Subclause("6.6.2"));
    }
  }
}

static void CheckResistiveBidirTerminals(const ModuleItem* item,
                                         const RtlirModule* mod,
                                         DiagEngine& diag) {
  const auto& terms = item->gate_terminals;
  for (size_t i = 0; i < 2; ++i) {
    auto* net = TerminalNet(terms[i], mod);
    if (net && net->is_user_nettype) {
      diag.Error(item->loc,
                 "resistive bidirectional pass switch terminal cannot "
                 "connect to a user-defined net type",
                 Subclause("28.8"));
      continue;
    }
    if (!IsScalarNetOrBitSelect(terms[i], mod)) {
      diag.Error(item->loc,
                 "resistive bidirectional pass switch terminal must be a "
                 "scalar net or a bit-select of a vector net",
                 Subclause("28.8"));
    }
  }
}

static void CheckBidirControlInputType(const ModuleItem* item,
                                       const RtlirModule* mod,
                                       DiagEngine& diag) {
  const auto& terms = item->gate_terminals;
  if (auto* bad = DisallowedControlVariableKind(terms[2], mod)) {
    diag.Error(item->loc,
               std::format("control input of pass-enable switch cannot be "
                           "of type '{}'; expected a 4-state net, 4-state "
                           "variable, or 2-state variable",
                           bad),
               Subclause("28.8"));
  }
}

static void CheckBidirNettypeCompatibility(
    const ModuleItem* item, const RtlirModule* mod, DiagEngine& diag,
    const std::unordered_map<std::string_view, std::string_view>&
        nettype_canonical) {
  const auto& terms = item->gate_terminals;
  auto* n0 = TerminalNet(terms[0], mod);
  auto* n1 = TerminalNet(terms[1], mod);
  if (!n0 || !n1) return;
  if (n0->is_user_nettype != n1->is_user_nettype) {
    diag.Error(item->loc,
               "bidirectional pass switch cannot connect a user-defined "
               "nettype to a built-in net",
               Subclause("28.8"));
    return;
  }
  // §6.22.6: two nettypes are the same when they match -- a nettype matches
  // itself and any renaming alias of it. Compare via the matching relation so
  // that an alias and its source nettype are treated as one type here.
  if (n0->is_user_nettype && n1->is_user_nettype &&
      !NettypesMatch(n0->nettype_name, n1->nettype_name, nettype_canonical)) {
    diag.Error(item->loc,
               std::format("bidirectional pass switch cannot connect "
                           "different user-defined nettypes ('{}' and '{}')",
                           n0->nettype_name, n1->nettype_name),
               Subclause("28.8"));
  }
}

void ValidateBidirectionalSwitchConnections(
    const ModuleItem* item, const RtlirModule* mod, DiagEngine& diag,
    const std::unordered_map<std::string_view, std::string_view>&
        nettype_canonical) {
  if (!item || item->kind != ModuleItemKind::kGateInst) return;
  auto kind = item->gate_kind;
  if (!IsBidirectionalSwitch(kind)) return;
  const auto& terms = item->gate_terminals;
  if (terms.size() < 2) return;

  CheckBidirUwireTerminals(item, mod, diag);

  if (IsResistiveBidirectionalSwitch(kind)) {
    CheckResistiveBidirTerminals(item, mod, diag);
  }

  if (IsControlBidirectionalSwitch(kind) && terms.size() >= 3) {
    CheckBidirControlInputType(item, mod, diag);
  }

  CheckBidirNettypeCompatibility(item, mod, diag, nettype_canonical);
}

static std::vector<size_t> OutputOrInoutTerminalIndices(GateKind kind,
                                                        size_t nterms) {
  switch (kind) {
    case GateKind::kBuf:
    case GateKind::kNot: {
      std::vector<size_t> outs;
      for (size_t i = 0; i + 1 < nterms; ++i) outs.push_back(i);
      return outs;
    }
    case GateKind::kTran:
    case GateKind::kRtran:
    case GateKind::kTranif0:
    case GateKind::kTranif1:
    case GateKind::kRtranif0:
    case GateKind::kRtranif1:

      return (nterms >= 2) ? std::vector<size_t>{0, 1} : std::vector<size_t>{};
    default:

      return (nterms >= 1) ? std::vector<size_t>{0} : std::vector<size_t>{};
  }
}

// §4.9.6 / §23.3.3: the elaboration-time bit width of a structural net
// expression when it is used as a primitive (gate/switch) output or inout
// terminal. A plain net identifier reports its declared width; a bit-select of
// a net is one bit; a ranged part-select `[msb:lsb]` or indexed part-select
// `[base +:/-: w]` reports its span when the bounds are constant; a
// concatenation reports the sum of its parts. Returns 0 when the width cannot
// be pinned down at elaboration (non-constant select bounds, or an expression
// outside the structural-net-expression grammar), so the 1-bit rule is left
// unenforced for that terminal rather than risk a false rejection.
static uint32_t StructuralNetExprWidth(const Expr* t, const RtlirModule* mod,
                                       const ScopeMap& scope);

// §28.3.1: the width a select contributes to a structural net expression. A
// bare bit-select is one bit; an indexed part-select carries its own constant
// width; a ranged part-select spans its two constant bounds. A bound that does
// not fold leaves the width unmeasured.
static uint32_t StructuralSelectWidth(const Expr* t, const ScopeMap& scope) {
  if (!t->index_end) return 1;  // bit-select -> exactly one bit
  if (t->is_part_select_plus || t->is_part_select_minus) {
    auto width = ConstEvalInt(t->index_end, scope);
    if (width && *width > 0) return static_cast<uint32_t>(*width);
    return 0;
  }
  auto hi = ConstEvalInt(t->index, scope);
  auto lo = ConstEvalInt(t->index_end, scope);
  if (!hi || !lo) return 0;
  int64_t span = (*hi >= *lo) ? (*hi - *lo) : (*lo - *hi);
  return static_cast<uint32_t>(span + 1);
}

// A concatenation is as wide as its parts together; an unmeasured part means
// the whole is unknown.
static uint32_t StructuralConcatWidth(const Expr* t, const RtlirModule* mod,
                                      const ScopeMap& scope) {
  uint32_t total = 0;
  for (const auto* e : t->elements) {
    uint32_t w = StructuralNetExprWidth(e, mod, scope);
    if (w == 0) return 0;
    total += w;
  }
  return total;
}

static uint32_t StructuralNetExprWidth(const Expr* t, const RtlirModule* mod,
                                       const ScopeMap& scope) {
  if (!t) return 0;
  switch (t->kind) {
    case ExprKind::kIdentifier:
      return LookupLhsWidth(t, mod);
    case ExprKind::kSelect:
      return StructuralSelectWidth(t, scope);
    case ExprKind::kConcatenation:
      return StructuralConcatWidth(t, mod, scope);
    default:
      return 0;
  }
}

// §29.8's `udp_instance ::= [ name_of_instance ] ( output_terminal ,
// input_terminal { , input_terminal } )` production puts the output terminal
// first, and §29.3.1 rules that "UDPs have multiple input ports and exactly one
// output port; bidirectional inout ports are not permitted on UDPs", so index 0
// is the whole answer. OutputOrInoutTerminalIndices cannot answer it:
// Parser::ParseOneUdpInstance (src/parser/parser_udp.cpp) never writes
// ModuleItem::gate_kind, so a primitive instance carries the GateKind::kAnd its
// declaration at src/parser/ast_module.h:302 defaults to, and the {0} that
// enumerator's default arm returns says nothing about a primitive.
static std::vector<size_t> UdpOutputTerminalIndices(size_t nterms) {
  return (nterms >= 1) ? std::vector<size_t>{0} : std::vector<size_t>{};
}

void ValidatePrimitiveOutputTerminalWidths(const ModuleItem* item,
                                           const RtlirModule* mod,
                                           const ScopeMap& scope,
                                           DiagEngine& diag) {
  // §4.9.6 states the rule this enforces for both kinds: "Primitive terminals,
  // including UDP terminals, are different from module ports. Primitive output
  // and inout terminals shall be connected directly to 1-bit nets or 1-bit
  // structural net expressions."
  if (!item || (item->kind != ModuleItemKind::kGateInst &&
                item->kind != ModuleItemKind::kUdpInst)) {
    return;
  }
  const bool kIsUdp = item->kind == ModuleItemKind::kUdpInst;

  // An instance array measures nothing here, for a primitive instance as for a
  // gate instance. §28.3.6 makes a terminal wider than one bit the distributed
  // connection -- "each instance shall get a part-select of the port
  // expression, of a bit length equal to the instance port bit length" -- so
  // the single bit §4.9.6 requires is what one element connects to, and the
  // whole terminal is not the width to measure. §29.8 rules of an array of
  // user-defined primitive instances that "The terminal connection rules remain
  // the same as outlined in 28.3.6", so the same reading holds for a kUdpInst
  // item. CheckGateInstanceArrayTerminalWidths (src/elaborator/
  // elaborator_items.cpp) is what checks these terminals instead.
  if (item->inst_range_left || item->inst_range_right) return;

  const auto& terms = item->gate_terminals;
  const std::vector<size_t> kOuts =
      kIsUdp ? UdpOutputTerminalIndices(terms.size())
             : OutputOrInoutTerminalIndices(item->gate_kind, terms.size());
  for (size_t i : kOuts) {
    auto* t = terms[i];
    if (!t) continue;
    uint32_t w = StructuralNetExprWidth(t, mod, scope);
    if (w == 0 || w == 1) continue;
    // A primitive instance is told about its output terminal alone, because
    // §29.3.1 permits a UDP no inout terminal and exactly one output. A gate
    // instance is told about both, because §28.3.6 puts "the output or
    // bidirectional terminals" first together and several gate types connect a
    // bidirectional one.
    const char* kTerminal = kIsUdp ? "user-defined primitive output terminal"
                                   : "primitive output or inout terminal";
    diag.Error(item->loc,
               std::format("{} must be a 1-bit net or structural net "
                           "expression (got width {})",
                           kTerminal, w),
               Subclause("4.9.6"));
  }
}

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

static Expr* WrapInvert(Arena& arena, Expr* inner) {
  auto* inv = arena.Create<Expr>();
  inv->kind = ExprKind::kUnary;
  inv->op = TokenKind::kTilde;
  inv->lhs = inner;
  return inv;
}

static Expr* MakeIntLiteral(Arena& arena, uint64_t val) {
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = val;
  return lit;
}

static Expr* MakeHighZ(Arena& arena) {
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kUnbasedUnsizedLiteral;
  lit->text = "'z";
  return lit;
}

static Expr* MakeTernary(Arena& arena, Expr* cond, Expr* t, Expr* f) {
  auto* tern = arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = cond;
  tern->true_expr = t;
  tern->false_expr = f;
  return tern;
}

static Expr* BuildNInputGateExpr(Arena& arena, GateKind kind,
                                 const std::vector<Expr*>& terminals) {
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

static void ApplyGateDelays(RtlirContAssign& ca, const ModuleItem* item) {
  ca.delay = item->gate_delay;
  ca.delay_fall = item->gate_delay_fall;
  ca.delay_decay = item->gate_delay_decay;
  ca.drive_strength0 = item->drive_strength0;
  ca.drive_strength1 = item->drive_strength1;
}

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

static void ElaborateBufNotGate(ModuleItem* item, RtlirModule* mod,
                                Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.size() < 2) return;
  auto* input = terms.back();
  for (size_t i = 0; i + 1 < terms.size(); ++i) {
    // §28.5 Table 28-4: buf and not are non-tristate drivers, so a
    // high-impedance (z) input yields an unknown (x) output rather than
    // propagating z. A single inversion already maps z->x (and x->x), so not
    // uses one complement and buf uses a double complement, which normalizes z
    // to x while leaving 0/1/x unchanged.
    Expr* rhs = (kind == GateKind::kNot)
                    ? WrapInvert(arena, input)
                    : WrapInvert(arena, WrapInvert(arena, input));
    RtlirContAssign ca;
    ca.lhs = terms[i];
    ca.rhs = rhs;
    ca.width = LookupLhsWidth(ca.lhs, mod);
    ApplyGateDelays(ca, item);
    mod->assigns.push_back(ca);
  }
}

static void ElaborateBufifNotifGate(ModuleItem* item, RtlirModule* mod,
                                    Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.size() != 3) return;
  auto* data = terms[1];
  auto* ctrl = terms[2];
  bool invert = (kind == GateKind::kNotif0 || kind == GateKind::kNotif1);
  bool conduct_on_one =
      (kind == GateKind::kBufif1 || kind == GateKind::kNotif1);
  // §28.6 Table 28-5: when the gate conducts, the data input drives the
  // output, but a high-impedance (z) data value cannot be transmitted and
  // emerges as x -- an unambiguous x, distinct from the L/H strength-ambiguous
  // results of an unknown control. Bitwise negation folds z to x while leaving
  // 0, 1, and x unchanged, so notif's single inversion already normalizes the
  // data, whereas a non-inverting bufif needs a double inversion to fold z to x
  // without inverting the transmitted value.
  Expr* pass = invert ? WrapInvert(arena, data)
                      : WrapInvert(arena, WrapInvert(arena, data));
  Expr* hi_z = MakeHighZ(arena);
  Expr* rhs = conduct_on_one ? MakeTernary(arena, ctrl, pass, hi_z)
                             : MakeTernary(arena, ctrl, hi_z, pass);
  RtlirContAssign ca;
  ca.lhs = terms[0];
  ca.rhs = rhs;
  ca.width = LookupLhsWidth(ca.lhs, mod);
  ApplyGateDelays(ca, item);
  mod->assigns.push_back(ca);
}

static void ElaborateMosGate(ModuleItem* item, RtlirModule* mod, Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.size() != 3) return;
  auto* data = terms[1];
  auto* ctrl = terms[2];
  bool conduct_on_one = (kind == GateKind::kNmos || kind == GateKind::kRnmos);
  Expr* hi_z = MakeHighZ(arena);
  Expr* rhs = conduct_on_one ? MakeTernary(arena, ctrl, data, hi_z)
                             : MakeTernary(arena, ctrl, hi_z, data);
  RtlirContAssign ca;
  ca.lhs = terms[0];
  ca.rhs = rhs;
  ca.width = LookupLhsWidth(ca.lhs, mod);

  ca.from_nonresistive_switch =
      (kind == GateKind::kNmos || kind == GateKind::kPmos);
  ca.from_resistive_switch =
      (kind == GateKind::kRnmos || kind == GateKind::kRpmos);
  if (ca.from_nonresistive_switch || ca.from_resistive_switch) {
    ca.data_input = data;
  }
  ApplyGateDelays(ca, item);
  mod->assigns.push_back(ca);
}

static void ElaboratePullGate(ModuleItem* item, RtlirModule* mod,
                              Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.size() != 1) return;
  bool is_up = (kind == GateKind::kPullup);
  uint8_t driving = is_up ? item->drive_strength1 : item->drive_strength0;
  if (driving == 0) driving = 3;
  RtlirContAssign ca;
  ca.lhs = terms[0];
  ca.rhs = MakeIntLiteral(arena, is_up ? 1 : 0);
  ca.width = LookupLhsWidth(ca.lhs, mod);
  ca.drive_strength0 = is_up ? 0 : driving;
  ca.drive_strength1 = is_up ? driving : 0;
  mod->assigns.push_back(ca);
}

static void ElaborateCmosGate(ModuleItem* item, RtlirModule* mod,
                              Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
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

  ca.from_nonresistive_switch = (kind == GateKind::kCmos);
  ca.from_resistive_switch = (kind == GateKind::kRcmos);
  if (ca.from_nonresistive_switch || ca.from_resistive_switch) {
    ca.data_input = data;
  }
  ApplyGateDelays(ca, item);
  mod->assigns.push_back(ca);
}

static void ElaborateLogicOrOutputGate(ModuleItem* item, RtlirModule* mod,
                                       Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
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

// `base[idx]`: the 1-bit part-select through which one element of an instance
// array connects to bit `idx` of a distributed terminal.
static Expr* MakeBitSelect(Arena& arena, Expr* base, uint32_t idx) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = MakeIntLiteral(arena, idx);
  return e;
}

// Elaborates one scalar gate or switch from the terminal list currently held on
// `item` (a single instance, or one element of an expanded instance array).
static void ElaborateOneGate(ModuleItem* item, RtlirModule* mod, Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.empty()) return;

  if (kind == GateKind::kBuf || kind == GateKind::kNot) {
    ElaborateBufNotGate(item, mod, arena);
    return;
  }

  if (kind == GateKind::kBufif0 || kind == GateKind::kBufif1 ||
      kind == GateKind::kNotif0 || kind == GateKind::kNotif1) {
    ElaborateBufifNotifGate(item, mod, arena);
    return;
  }

  if (IsBidirectionalSwitch(kind)) {
    return;
  }

  if (kind == GateKind::kNmos || kind == GateKind::kPmos ||
      kind == GateKind::kRnmos || kind == GateKind::kRpmos) {
    ElaborateMosGate(item, mod, arena);
    return;
  }

  if (kind == GateKind::kPullup || kind == GateKind::kPulldown) {
    ElaboratePullGate(item, mod, arena);
    return;
  }

  if (kind == GateKind::kCmos || kind == GateKind::kRcmos) {
    ElaborateCmosGate(item, mod, arena);
    return;
  }

  ElaborateLogicOrOutputGate(item, mod, arena);
}

// The terminal list one element of an instance array connects to: a terminal
// as wide as the array takes its [p] bit-select, and a single-bit terminal is
// broadcast unchanged.
static std::vector<Expr*> InstanceArrayElementTerminals(
    const std::vector<Expr*>& terms, const RtlirModule* mod, Arena& arena,
    uint32_t array_len, uint32_t p) {
  std::vector<Expr*> bit_terms;
  bit_terms.reserve(terms.size());
  for (auto* t : terms)
    bit_terms.push_back(
        LookupLhsWidth(t, mod) == array_len ? MakeBitSelect(arena, t, p) : t);
  return bit_terms;
}

bool ExpandInstanceArray(
    ModuleItem* item, const RtlirModule* mod, Arena& arena,
    const std::function<void(ModuleItem*)>& elaborate_element) {
  uint32_t array_len = 0;
  for (auto* t : item->gate_terminals)
    array_len = std::max(array_len, LookupLhsWidth(t, mod));
  if (array_len <= 1) return false;
  std::vector<Expr*> saved = item->gate_terminals;
  for (uint32_t p = 0; p < array_len; ++p) {
    item->gate_terminals =
        InstanceArrayElementTerminals(saved, mod, arena, array_len, p);
    elaborate_element(item);
  }
  item->gate_terminals = saved;
  return true;
}

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena) {
  // §28.3.6: an instance array whose terminals carry more than one bit is
  // expanded into one scalar primitive per array element. Rebuilding each
  // element from bit-selects reproduces the per-element connection for every
  // gate family, including the control-driven three-state and MOS switches
  // whose vector control would otherwise collapse to one scalar condition
  // shared across the whole array.
  if (item->inst_range_left && item->inst_range_right &&
      ExpandInstanceArray(item, mod, arena, [mod, &arena](ModuleItem* element) {
        ElaborateOneGate(element, mod, arena);
      }))
    return;

  ElaborateOneGate(item, mod, arena);
}

}  // namespace delta
