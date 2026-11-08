#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <span>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_attribute.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/uwire_drivers.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

void Elaborator::ValidateContAssignIdentLhs(std::string_view name,
                                            ModuleItem* item,
                                            RtlirModule* mod) {
  MaybeCreateImplicitNet(name, item->loc, mod);
  std::string_view declared =
      DeclaredScopedName(name, gen_prefix_scopes_, declared_names_);
  if (!cont_assign_targets_.emplace(declared, item->loc).second &&
      !NamesNet(name, item->loc)) {
    diag_.Error(item->loc,
                std::format("multiple continuous assignments to '{}'", name),
                Subclause("6.5"));
  }
}

void Elaborator::ValidateContAssignDriveStrength(ModuleItem* item,
                                                 RtlirModule* mod) {
  const Expr* lhs = item->assign_lhs;
  std::string_view root = LhsBaseName(lhs);
  for (const auto& n : mod->nets) {
    if (n.name != root) continue;
    if (n.net_type != NetType::kSupply0 && n.net_type != NetType::kSupply1)
      break;
    diag_.Error(item->loc,
                "drive strength on continuous assignment does not apply to "
                "supply0 or supply1 nets",
                Subclause("10.3.4"));
    return;
  }
  if (lhs->kind == ExprKind::kIdentifier && LookupLhsWidth(lhs, mod) <= 1)
    return;
  diag_.Error(item->loc,
              "drive strength on continuous assignment applies only to "
              "scalar nets",
              Subclause("10.3.4"));
}

namespace {

void ValidateContAssignVarTarget(ModuleItem* item, DiagEngine& diag) {
  if (item->drive_strength0 != 0 || item->drive_strength1 != 0) {
    diag.Error(item->loc,
               "drive strength not allowed on continuous assignment "
               "to a variable",
               Subclause("10.3.4"));
  }
  if (item->assign_delay_fall || item->assign_delay_decay) {
    diag.Error(item->loc,
               "multiple delays not allowed on continuous assignment "
               "to a variable",
               Subclause("10.3.3"));
  }
}

RtlirContAssign BuildContAssignFor(
    ModuleItem* item, Expr* lhs, Expr* rhs, uint32_t width,
    const std::vector<ResolvedAttribute>& attrs) {
  RtlirContAssign ca;
  ca.lhs = lhs;
  ca.rhs = rhs;
  ca.source_item = item;
  ca.width = width;
  ca.drive_strength0 = item->drive_strength0;
  ca.drive_strength1 = item->drive_strength1;
  ca.delay = item->assign_delay;
  ca.delay_fall = item->assign_delay_fall;
  ca.delay_decay = item->assign_delay_decay;
  ca.attrs = attrs;
  return ca;
}

RtlirContAssign BuildContAssign(ModuleItem* item, RtlirModule* mod,
                                const std::vector<ResolvedAttribute>& attrs) {
  return BuildContAssignFor(item, item->assign_lhs, item->assign_rhs,
                            LookupLhsWidth(item->assign_lhs, mod), attrs);
}

}  // namespace

uint32_t SelectLhsWidth(const Expr* e, const ScopeMap& scope) {
  if (e->index == nullptr) return 0;
  if (e->index_end == nullptr) return 1;
  if (e->is_part_select_plus || e->is_part_select_minus) {
    auto w = ConstEvalInt(e->index_end, scope);
    return (w && *w > 0) ? static_cast<uint32_t>(*w) : 0;
  }
  auto msb = ConstEvalInt(e->index, scope);
  auto lsb = ConstEvalInt(e->index_end, scope);
  if (!msb || !lsb) return 0;
  return static_cast<uint32_t>(std::abs(*msb - *lsb) + 1);
}

namespace {

uint32_t ConcatLhsWidth(const Expr* e, const RtlirModule* mod,
                        const ScopeMap& scope) {
  if (e->kind == ExprKind::kSelect) return SelectLhsWidth(e, scope);
  if (e->kind != ExprKind::kConcatenation) return LookupLhsWidth(e, mod);
  uint32_t total = 0;
  for (const auto* sub : e->elements) total += ConcatLhsWidth(sub, mod, scope);
  return total;
}

Expr* MakeRhsPartSelect(Expr* rhs, int64_t first, int64_t second,
                        Arena& arena) {
  auto* hi_lit = arena.Create<Expr>();
  hi_lit->kind = ExprKind::kIntegerLiteral;
  hi_lit->int_val = static_cast<uint64_t>(first);
  auto* lo_lit = arena.Create<Expr>();
  lo_lit->kind = ExprKind::kIntegerLiteral;
  lo_lit->int_val = static_cast<uint64_t>(second);
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = rhs;
  sel->index = hi_lit;
  sel->index_end = lo_lit;
  return sel;
}

struct ConcatContAssignCtx {
  ModuleItem* item;
  RtlirModule* mod;
  Arena& arena;
  const std::vector<ResolvedAttribute>& attrs;
  const ScopeMap& scope;
};

PackedRange RhsSelectRange(const Expr* rhs, uint32_t width,
                           const ConcatContAssignCtx& cx) {
  if (rhs && rhs->kind == ExprKind::kIdentifier) {
    return SignalDeclaredRange(rhs->text, cx.mod, cx.scope);
  }
  return PackedRange::Implicit(width);
}

Expr* MakeWidenedRhs(Expr* rhs, uint32_t width, Arena& arena) {
  std::string text = std::format("{}'sd0", width);
  auto* zero = arena.Create<Expr>();
  zero->kind = ExprKind::kIntegerLiteral;
  zero->text = {arena.AllocString(text.c_str(), text.size()), text.size()};
  zero->range = rhs->range;
  auto* sum = arena.Create<Expr>();
  sum->kind = ExprKind::kBinary;
  sum->op = TokenKind::kPlus;
  sum->lhs = rhs;
  sum->rhs = zero;
  sum->range = rhs->range;
  return sum;
}

void EmitConcatContAssigns(const ConcatContAssignCtx& cx, Expr* lhs,
                           Expr* rhs) {
  uint32_t hi = ConcatLhsWidth(lhs, cx.mod, cx.scope);
  if (hi == 0 || rhs == nullptr) return;
  uint32_t named_width =
      rhs->kind == ExprKind::kIdentifier ? LookupLhsWidth(rhs, cx.mod) : 0;
  Expr* source = named_width >= hi ? rhs : MakeWidenedRhs(rhs, hi, cx.arena);
  PackedRange range = RhsSelectRange(source, hi, cx);
  for (auto* el : lhs->elements) {
    uint32_t w = ConcatLhsWidth(el, cx.mod, cx.scope);
    if (w == 0) continue;
    Expr* elem_rhs = MakeRhsPartSelect(source, range.IndexAtOffset(hi - 1),
                                       range.IndexAtOffset(hi - w), cx.arena);
    hi -= w;
    if (el->kind == ExprKind::kConcatenation) {
      EmitConcatContAssigns(cx, el, elem_rhs);
    } else {
      cx.mod->assigns.push_back(
          BuildContAssignFor(cx.item, el, elem_rhs, w, cx.attrs));
    }
  }
}

}  // namespace

struct ContTargetLeaf {
  const Expr* expr = nullptr;
  std::string_view root = {};
  size_t selects = 0;
  bool has_member = false;
};

static ContTargetLeaf LeafOf(const Expr* e) {
  ContTargetLeaf leaf{.expr = e};
  while (e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess) {
    if (e->kind == ExprKind::kMemberAccess) {
      leaf.has_member = true;
      leaf.selects = 0;
      e = e->lhs;
    } else {
      ++leaf.selects;
      e = e->base;
    }
  }
  if (e->kind == ExprKind::kIdentifier) leaf.root = e->text;
  return leaf;
}

static bool CollectContTargetLeaves(const Expr* e,
                                    std::vector<ContTargetLeaf>& out) {
  if (e->is_parenthesized) return false;
  if (e->kind == ExprKind::kCast &&
      e->lhs->kind == ExprKind::kAssignmentPattern)
    e = e->lhs;
  if (e->kind == ExprKind::kConcatenation ||
      e->kind == ExprKind::kAssignmentPattern) {
    for (const Expr* el : e->elements)
      if (!CollectContTargetLeaves(el, out)) return false;
    return true;
  }
  if (e->kind == ExprKind::kStreamingConcat) return true;
  ContTargetLeaf leaf = LeafOf(e);
  if (leaf.root.empty()) return false;
  out.push_back(leaf);
  return true;
}

static bool NamesParameter(std::string_view name, const RtlirModule* mod,
                           const std::vector<std::string_view>& scopes) {
  for (const auto& p : mod->params) {
    if (p.name == name && ParamVisibleFromScopes(p.gen_block_prefix, scopes))
      return true;
  }
  return false;
}

void ValidatePrimitiveDrivenTerminals(
    const ModuleItem* item, const RtlirModule* mod, const ScopeMap& scope,
    const std::vector<std::string_view>& gen_scopes, DiagEngine& diag) {
  std::vector<ContTargetLeaf> leaves;
  for (size_t i : PrimitiveDrivenTerminalIndices(item)) {
    if (item->gate_terminals[i] == nullptr) continue;
    CollectContTargetLeaves(item->gate_terminals[i], leaves);
  }
  for (const ContTargetLeaf& leaf : leaves) {
    if (NamesParameter(leaf.root, mod, gen_scopes)) {
      diag.Error(item->loc,
                 std::format("a primitive's output or inout terminal names "
                             "parameter '{}', a constant no primitive drives",
                             leaf.root),
                 Subclause("A.8.5"));
    } else if (!SelectPathIsConstant(leaf.expr, scope)) {
      diag.Error(item->loc,
                 "a primitive's output or inout terminal selects with an "
                 "expression that is not constant",
                 Subclause("A.8.5"));
    }
  }
}

static size_t UnpackedDimsOfNet(std::string_view name, const RtlirModule* mod) {
  for (const auto& n : mod->nets)
    if (n.name == name) return n.num_unpacked_dims;
  return 0;
}

static void ReportContTargetInitializer(
    const ModuleItem* item, std::string_view name, std::string_view declared,
    const std::unordered_set<std::string_view>& var_init_names,
    DiagEngine& diag) {
  if (var_init_names.count(declared) == 0) return;
  diag.Error(item->loc,
             std::format("variable '{}' has both an initializer and a "
                         "continuous assignment",
                         name),
             Subclause("10.3.2"));
}

bool Elaborator::ValidateContAssignLeaf(ModuleItem* item, RtlirModule* mod,
                                        const ContTargetLeaf& leaf,
                                        const ScopeMap& scope) {
  if (NamesParameter(leaf.root, mod, gen_prefix_scopes_)) {
    diag_.Error(
        item->loc,
        std::format("continuous assignment to parameter '{}'", leaf.root),
        Subclause("10.3"));
    return false;
  }
  if (!SelectPathIsConstant(leaf.expr, scope)) {
    diag_.Error(item->loc,
                "continuous assignment left-hand side requires a "
                "constant select expression",
                Subclause("10.3.2"));
  }
  if (leaf.expr->kind == ExprKind::kIdentifier)
    ValidateContAssignIdentLhs(leaf.root, item, mod);
  RecordUwireTarget(uwire_drivers_, leaf.expr, item->loc,
                    {mod,
                     var_types_,
                     unit_,
                     unit_uwire_drivers_,
                     {gen_prefix_scopes_, declared_names_},
                     scope},
                    diag_);
  bool is_net = NamesNet(leaf.root, item->loc);
  bool is_var = !is_net && !leaf.has_member;
  if (is_var) ValidateContAssignVarLeaf(item, leaf.root);
  if (nettype_net_names_.count(leaf.root) != 0 &&
      (leaf.has_member || leaf.selects > UnpackedDimsOfNet(leaf.root, mod))) {
    diag_.Error(item->loc,
                "a continuous assignment to a net of a user-defined nettype "
                "drives the whole net and cannot index or select into it",
                Subclause("10.3.2"));
  }
  bool is_var_member = !is_var && !is_net && var_types_.count(leaf.root) != 0;
  if (is_var_member) {
    ReportContTargetInitializer(
        item, leaf.root,
        DeclaredScopedName(leaf.root, gen_prefix_scopes_, declared_names_),
        var_init_names_, diag_);
  }
  return is_var || is_var_member;
}

void Elaborator::ValidateContAssignVarLeaf(ModuleItem* item,
                                           std::string_view name) {
  std::string_view declared =
      DeclaredScopedName(name, gen_prefix_scopes_, declared_names_);
  if (!gen_prefix_scopes_.empty() &&
      proc_assign_targets_.count(declared) != 0) {
    diag_.Error(item->loc,
                std::format("variable '{}' has both continuous and "
                            "procedural assignments",
                            name),
                Subclause("6.5"));
    ReportForcesOverMixture(declared, name);
  }
  ReportContTargetInitializer(item, name, declared, var_init_names_, diag_);
}

bool Elaborator::ValidateContAssignLeaves(
    ModuleItem* item, RtlirModule* mod,
    const std::vector<ContTargetLeaf>& leaves) {
  ScopeMap scope = BuildParamScope(mod);
  for (const auto& [name, value] : gen_const_scope_) scope[name] = value;
  bool any_var = false;
  for (const ContTargetLeaf& leaf : leaves) {
    if (ValidateContAssignLeaf(item, mod, leaf, scope)) any_var = true;
  }
  return any_var;
}

void CheckHighzStrengthPair(const ModuleItem* item, DiagEngine& diag) {
  if ((item->kind == ModuleItemKind::kNetDecl ||
       item->kind == ModuleItemKind::kContAssign ||
       item->kind == ModuleItemKind::kGateInst ||
       item->kind == ModuleItemKind::kUdpInst) &&
      item->drive_strength0 == 1 && item->drive_strength1 == 1) {
    diag.Error(item->loc, "drive strength (highz0, highz1) is illegal",
               Subclause("28.3.2"));
  }
}

void Elaborator::ValidateGeneratedItem(const ModuleItem* item,
                                       const RtlirModule& mod) {
  CheckHighzStrengthPair(item, diag_);
  ValidateItemRules(item, mod, BuildParamScope(&mod));
  if (!IsProceduralItemKind(item->kind)) return;
  std::unordered_map<std::string_view, SourceLoc> targets;
  CollectProcTargets({}, {item->body}, targets);
  std::unordered_map<std::string_view, SourceLoc> assigned;
  CollectProcContAssignTargets({}, {item->body}, assigned);
  for (const auto& [name, loc] : assigned) {
    if (!NamesNet(name, loc)) targets.emplace(name, loc);
  }
  for (const auto& [name, loc] : targets) {
    if (NamesNet(name, loc)) {
      diag_.Error(loc,
                  std::format("net '{}' cannot be the target of a "
                              "procedural assignment",
                              name),
                  Subclause("10.4"));
      continue;
    }
    RecordProcTarget(name, loc);
  }
  std::unordered_map<std::string_view, SourceLoc> forced;
  CollectForceReleaseTargets(item->body, forced);
  for (const auto& [name, loc] : forced) {
    std::string_view declared =
        DeclaredScopedName(name, gen_prefix_scopes_, declared_names_);
    force_release_targets_.emplace(declared, loc);
    if (cont_assign_targets_.count(declared) != 0 &&
        proc_assign_targets_.count(declared) != 0) {
      ReportForceOverMixture(name, loc, diag_);
    }
  }
}

void Elaborator::RecordProcTarget(std::string_view name, SourceLoc loc) {
  std::string_view declared =
      DeclaredScopedName(name, gen_prefix_scopes_, declared_names_);
  if (!gen_prefix_scopes_.empty() &&
      cont_assign_targets_.count(declared) != 0) {
    diag_.Error(loc,
                std::format("variable '{}' has both continuous and "
                            "procedural assignments",
                            name),
                Subclause("6.5"));
    ReportForcesOverMixture(declared, name);
  }
  proc_assign_targets_.emplace(declared, loc);
}

void Elaborator::ReportForcesOverMixture(std::string_view declared,
                                         std::string_view name) {
  auto force = force_release_targets_.find(declared);
  if (force != force_release_targets_.end()) {
    ReportForceOverMixture(name, force->second, diag_);
  }
}

std::span<Expr* const> PrimitiveOutputTerminals(const ModuleItem* item) {
  const std::vector<Expr*>& terminals = item->gate_terminals;
  if (terminals.empty()) return {};
  bool n_output =
      item->kind == ModuleItemKind::kGateInst &&
      (item->gate_kind == GateKind::kBuf || item->gate_kind == GateKind::kNot);
  return {terminals.data(), n_output ? terminals.size() - 1 : 1};
}

void Elaborator::RecordGateOutputDrivers(const ModuleItem* item) {
  for (const Expr* terminal : PrimitiveOutputTerminals(item)) {
    std::string_view name = ExprIdent(terminal);
    if (name.empty() || NamesNet(name, item->loc)) continue;
    std::string_view declared =
        DeclaredScopedName(name, gen_prefix_scopes_, declared_names_);
    if (!cont_assign_targets_.emplace(declared, item->loc).second) {
      diag_.Error(item->loc,
                  std::format("variable '{}' is driven by more than one "
                              "continuous assignment or primitive output",
                              name),
                  Subclause("10.3.2"));
    }
    if (var_init_names_.count(declared) != 0) {
      diag_.Error(item->loc,
                  std::format("variable '{}' has both an initializer and a "
                              "primitive output driving it",
                              name),
                  Subclause("10.3.2"));
    }
  }
}

static bool ReachesAnotherScope(
    const std::vector<ContTargetLeaf>& leaves,
    const std::unordered_set<std::string_view>& net_names) {
  return std::ranges::any_of(leaves, [&](const ContTargetLeaf& leaf) {
    return leaf.has_member && net_names.count(leaf.root) == 0;
  });
}

static void ReportStreamTargetNets(
    const Expr* e, const std::unordered_set<std::string_view>& net_names,
    SourceLoc loc, DiagEngine& diag) {
  if (e->kind == ExprKind::kStreamingConcat ||
      e->kind == ExprKind::kConcatenation) {
    for (const Expr* el : e->elements)
      ReportStreamTargetNets(el, net_names, loc, diag);
    return;
  }
  std::string_view name = LhsBaseName(e);
  if (net_names.count(name) == 0) return;
  diag.Error(loc,
             std::format("a streaming concatenation written as a target "
                         "unpacks into variables, and '{}' is a net",
                         name),
             Subclause("11.4.14.3"));
}

void Elaborator::ElaborateContAssign(ModuleItem* item, RtlirModule* mod) {
  ValidateInterconnectContAssign(item);
  std::vector<ContTargetLeaf> leaves;
  if (!CollectContTargetLeaves(item->assign_lhs, leaves)) {
    diag_.Error(item->loc,
                "continuous assignment target is not a net or variable "
                "lvalue",
                Subclause("10.3"));
    return;
  }
  bool streaming = item->assign_lhs->kind == ExprKind::kStreamingConcat;
  if (streaming)
    ReportStreamTargetNets(item->assign_lhs, NetNamesAt(item->loc), item->loc,
                           diag_);
  if (ValidateContAssignLeaves(item, mod, leaves) || streaming) {
    ValidateContAssignVarTarget(item, diag_);
  } else if ((item->drive_strength0 != 0 || item->drive_strength1 != 0) &&
             !ReachesAnotherScope(leaves, net_names_)) {
    ValidateContAssignDriveStrength(item, mod);
  }
  if (item->assign_lhs->kind == ExprKind::kIdentifier &&
      nettype_net_names_.count(item->assign_lhs->text) != 0 &&
      (item->assign_delay_fall || item->assign_delay_decay)) {
    diag_.Error(item->loc,
                "continuous assignment to a nettype net shall have at most "
                "a single delay",
                Subclause("10.3.3"));
  }
  ValidateGetpatternContAssign(item, mod);
  ScopeMap scope = BuildParamScope(mod);
  const std::vector<ResolvedAttribute> kAttrs =
      ResolveAttributes(item->attrs, diag_, scope);
  if (item->assign_lhs->kind == ExprKind::kConcatenation) {
    ConcatContAssignCtx cx{item, mod, arena_, kAttrs, scope};
    EmitConcatContAssigns(cx, item->assign_lhs, item->assign_rhs);
    return;
  }
  mod->assigns.push_back(BuildContAssign(item, mod, kAttrs));
}

}  // namespace delta
