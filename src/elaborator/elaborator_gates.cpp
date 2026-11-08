#include <cstdint>
#include <cstdlib>
#include <format>
#include <functional>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_gate_array_terminals.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_gate_type.h"
#include "parser/ast_module.h"

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
  GateType type = GateTypeOf(kind);
  return type == GateType::kPassSwitch || type == GateType::kPassEnSwitch;
}

static bool IsResistiveBidirectionalSwitch(GateKind kind) {
  return (kind == GateKind::kRtran || kind == GateKind::kRtranif0 ||
          kind == GateKind::kRtranif1);
}

static bool IsControlBidirectionalSwitch(GateKind kind) {
  return GateTypeOf(kind) == GateType::kPassEnSwitch;
}

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
                 "a resistive bidirectional pass switch terminal connects to a "
                 "single bit: a scalar net or one bit selected from a vector "
                 "net",
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
  switch (GateTypeOf(kind)) {
    case GateType::kNOutputGate: {
      std::vector<size_t> outs;
      for (size_t i = 0; i + 1 < nterms; ++i) outs.push_back(i);
      return outs;
    }
    case GateType::kPassSwitch:
    case GateType::kPassEnSwitch:
      return (nterms >= 2) ? std::vector<size_t>{0, 1} : std::vector<size_t>{};
    default:
      return (nterms >= 1) ? std::vector<size_t>{0} : std::vector<size_t>{};
  }
}

struct TerminalScope {
  const RtlirModule* mod;
  const ScopeMap& scope;
  const ScopedDeclarations& names;
};

static uint32_t StructuralNetExprWidth(const Expr* t,
                                       const TerminalScope& where);

static uint32_t StructuralSelectWidth(const Expr* t, const ScopeMap& scope) {
  if (!t->index_end) return 1;
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

static uint32_t StructuralConcatWidth(const Expr* t,
                                      const TerminalScope& where) {
  uint32_t total = 0;
  for (const auto* e : t->elements) {
    uint32_t w = StructuralNetExprWidth(e, where);
    if (w == 0) return 0;
    total += w;
  }
  return total;
}

static uint32_t StructuralNetExprWidth(const Expr* t,
                                       const TerminalScope& where) {
  if (!t) return 0;
  switch (t->kind) {
    case ExprKind::kIdentifier:
      return LookupNameWidth(
          DeclaredScopedName(t->text, where.names.scopes, where.names.declared),
          where.mod);
    case ExprKind::kSelect:
      return StructuralSelectWidth(t, where.scope);
    case ExprKind::kConcatenation:
      return StructuralConcatWidth(t, where);
    default:
      return 0;
  }
}

static std::vector<size_t> UdpOutputTerminalIndices(size_t nterms) {
  return (nterms >= 1) ? std::vector<size_t>{0} : std::vector<size_t>{};
}

std::vector<size_t> PrimitiveDrivenTerminalIndices(const ModuleItem* item) {
  const size_t kCount = item->gate_terminals.size();
  if (item->kind == ModuleItemKind::kUdpInst)
    return UdpOutputTerminalIndices(kCount);
  return OutputOrInoutTerminalIndices(item->gate_kind, kCount);
}

void ValidatePrimitiveOutputTerminalWidths(const ModuleItem* item,
                                           const RtlirModule* mod,
                                           const ScopeMap& scope,
                                           const ScopedDeclarations& names,
                                           DiagEngine& diag) {
  if (!item || (item->kind != ModuleItemKind::kGateInst &&
                item->kind != ModuleItemKind::kUdpInst)) {
    return;
  }
  const bool kIsUdp = item->kind == ModuleItemKind::kUdpInst;

  if (item->inst_range_left || item->inst_range_right) return;

  const auto& terms = item->gate_terminals;
  for (size_t i : PrimitiveDrivenTerminalIndices(item)) {
    auto* t = terms[i];
    if (!t) continue;
    uint32_t w = StructuralNetExprWidth(t, {mod, scope, names});
    if (w == 0 || w == 1) continue;
    const char* terminal = kIsUdp ? "user-defined primitive output terminal"
                                  : "primitive output or inout terminal";
    diag.Error(item->loc,
               std::format("{} must be a 1-bit net or structural net "
                           "expression (got width {})",
                           terminal, w),
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
  if (inputs.size() == 1 && !invert) {
    chain = WrapInvert(arena, WrapInvert(arena, chain));
  }
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
  Expr* pass = invert ? WrapInvert(arena, data)
                      : WrapInvert(arena, WrapInvert(arena, data));
  Expr* hi_z = MakeHighZ(arena);
  Expr* rhs = conduct_on_one ? MakeTernary(arena, ctrl, pass, hi_z)
                             : MakeTernary(arena, ctrl, hi_z, pass);
  RtlirContAssign ca;
  ca.lhs = terms[0];
  ca.rhs = rhs;
  ca.width = LookupLhsWidth(ca.lhs, mod);
  ca.three_state_ctrl = ctrl;
  ca.three_state_pass = pass;
  ApplyGateDelays(ca, item);
  mod->assigns.push_back(ca);
}

struct MosSwitch {
  Expr* out;
  Expr* data;
  Expr* ctrl;
  bool conducts_on_one;
  bool resistive;
};

static void EmitMosSwitch(const MosSwitch& sw, const ModuleItem* item,
                          RtlirModule* mod, Arena& arena) {
  Expr* conducting =
      sw.conducts_on_one
          ? MakeTernary(arena, sw.ctrl, sw.data, MakeHighZ(arena))
          : MakeTernary(arena, sw.ctrl, MakeHighZ(arena), sw.data);
  auto* data_is_z = arena.Create<Expr>();
  data_is_z->kind = ExprKind::kBinary;
  data_is_z->op = TokenKind::kEqEqEq;
  data_is_z->lhs = sw.data;
  data_is_z->rhs = MakeHighZ(arena);
  RtlirContAssign ca;
  ca.lhs = sw.out;
  ca.rhs = MakeTernary(arena, data_is_z, MakeHighZ(arena), conducting);
  ca.width = LookupLhsWidth(ca.lhs, mod);
  ca.from_nonresistive_switch = !sw.resistive;
  ca.from_resistive_switch = sw.resistive;
  ca.data_input = sw.data;
  ca.three_state_ctrl = sw.ctrl;
  ca.three_state_pass = sw.data;
  ApplyGateDelays(ca, item);
  mod->assigns.push_back(ca);
}

static void ElaborateMosGate(ModuleItem* item, RtlirModule* mod, Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.size() != 3) return;
  EmitMosSwitch({terms[0], terms[1], terms[2],
                 kind == GateKind::kNmos || kind == GateKind::kRnmos,
                 kind == GateKind::kRnmos || kind == GateKind::kRpmos},
                item, mod, arena);
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
  auto& terms = item->gate_terminals;
  if (terms.size() != 4) return;
  bool resistive = item->gate_kind == GateKind::kRcmos;
  EmitMosSwitch({terms[0], terms[1], terms[2], true, resistive}, item, mod,
                arena);
  EmitMosSwitch({terms[0], terms[1], terms[3], false, resistive}, item, mod,
                arena);
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

static void ElaborateBidirSwitch(ModuleItem* item, RtlirModule* mod) {
  auto& terms = item->gate_terminals;
  if (terms.size() < 2) return;
  RtlirBidirSwitch sw;
  sw.kind = item->gate_kind;
  sw.terminal_a = terms[0];
  sw.terminal_b = terms[1];
  if (IsControlBidirectionalSwitch(item->gate_kind) && terms.size() >= 3) {
    sw.control = terms[2];
  }
  sw.turn_on_delay = item->gate_delay;
  sw.turn_off_delay = item->gate_delay_fall;
  mod->bidir_switches.push_back(sw);
}

static void ElaborateOneGate(ModuleItem* item, RtlirModule* mod, Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.empty()) return;

  GateType type = GateTypeOf(kind);
  if (type == GateType::kNOutputGate) {
    ElaborateBufNotGate(item, mod, arena);
    return;
  }

  if (type == GateType::kEnableGate) {
    ElaborateBufifNotifGate(item, mod, arena);
    return;
  }

  if (IsBidirectionalSwitch(kind)) {
    ElaborateBidirSwitch(item, mod);
    return;
  }

  if (type == GateType::kMosSwitch) {
    ElaborateMosGate(item, mod, arena);
    return;
  }

  if (type == GateType::kPullGate) {
    ElaboratePullGate(item, mod, arena);
    return;
  }

  if (type == GateType::kCmosSwitch) {
    ElaborateCmosGate(item, mod, arena);
    return;
  }

  ElaborateLogicOrOutputGate(item, mod, arena);
}

std::optional<uint32_t> InstanceArrayLength(const ModuleItem* item,
                                            const ScopeMap& scope) {
  if (item->inst_range_left == nullptr || item->inst_range_right == nullptr) {
    return std::nullopt;
  }
  auto lhi = ConstEvalInt(item->inst_range_left, scope);
  auto rhi = ConstEvalInt(item->inst_range_right, scope);
  if (!lhi || !rhi) return std::nullopt;
  return static_cast<uint32_t>(std::abs(*lhi - *rhi) + 1);
}

bool ExpandInstanceArray(
    ModuleItem* item, const RtlirModule* mod, Arena& arena,
    const ScopeMap& scope,
    const std::function<void(ModuleItem*)>& elaborate_element) {
  auto len = InstanceArrayLength(item, scope);
  if (!len) return false;
  uint32_t array_len = *len;
  if (array_len <= 1) return false;
  std::vector<Expr*> saved = item->gate_terminals;
  for (uint32_t p = 0; p < array_len; ++p) {
    item->gate_terminals =
        InstanceArrayElementTerminals(saved, {mod, scope, arena}, array_len, p);
    elaborate_element(item);
  }
  item->gate_terminals = saved;
  return true;
}

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena,
                       const ScopeMap& scope) {
  mod->gate_insts.push_back(item);

  if (ExpandInstanceArray(item, mod, arena, scope,
                          [mod, &arena](ModuleItem* element) {
                            ElaborateOneGate(element, mod, arena);
                          }))
    return;

  ElaborateOneGate(item, mod, arena);
}

}  // namespace delta
