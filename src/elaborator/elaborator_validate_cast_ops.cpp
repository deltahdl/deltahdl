#include <charconv>
#include <format>
#include <optional>
#include <set>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::WalkExprForCast(const Expr* expr) {
  if (!expr) return;
  CheckCastExpr(expr);
  WalkExprForCast(expr->lhs);
  WalkExprForCast(expr->rhs);
  WalkExprForCast(expr->base);
  WalkExprForCast(expr->index);
  WalkExprForCast(expr->index_end);
  WalkExprForCast(expr->condition);
  WalkExprForCast(expr->true_expr);
  WalkExprForCast(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForCast(elem);
  for (auto* arg : expr->args) WalkExprForCast(arg);
}

void Elaborator::WalkStmtsForCast(const Stmt* s) {
  if (!s) return;
  WalkExprForCast(s->rhs);
  WalkExprForCast(s->lhs);
  WalkExprForCast(s->expr);
  WalkExprForCast(s->condition);
  WalkExprForCast(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForCast(sub);
  WalkStmtsForCast(s->then_branch);
  WalkStmtsForCast(s->else_branch);
  WalkStmtsForCast(s->body);
  WalkStmtsForCast(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForCast(ci.body);
}

void Elaborator::ValidateCastOperations(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForCast(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForCast(item->assign_lhs);
      WalkExprForCast(item->assign_rhs);
    }
  }
}

static bool IsAssignOp(TokenKind op) {
  switch (op) {
    case TokenKind::kEq:
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

void Elaborator::WalkExprForAssignInExpr(const Expr* expr,
                                         bool in_event_or_cont) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary && IsAssignOp(expr->op)) {
    if (in_event_or_cont) {
      diag_.Error(expr->range.start,
                  "assignment operator within expression is illegal in "
                  "this context",
                  Subclause::Unread());
    }
  }
  WalkExprForAssignInExpr(expr->lhs, in_event_or_cont);
  WalkExprForAssignInExpr(expr->rhs, in_event_or_cont);
  WalkExprForAssignInExpr(expr->condition, in_event_or_cont);
  WalkExprForAssignInExpr(expr->true_expr, in_event_or_cont);
  WalkExprForAssignInExpr(expr->false_expr, in_event_or_cont);
  for (auto* elem : expr->elements)
    WalkExprForAssignInExpr(elem, in_event_or_cont);
  for (auto* arg : expr->args) WalkExprForAssignInExpr(arg, in_event_or_cont);
}

void Elaborator::WalkStmtsForAssignInExpr(const Stmt* s) {
  if (!s) return;

  if (s->kind == StmtKind::kAssign && s->rhs) {
    WalkExprForAssignInExpr(s->rhs, true);
  }
  for (auto* sub : s->stmts) WalkStmtsForAssignInExpr(sub);
  WalkStmtsForAssignInExpr(s->then_branch);
  WalkStmtsForAssignInExpr(s->else_branch);
  WalkStmtsForAssignInExpr(s->body);
  WalkStmtsForAssignInExpr(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAssignInExpr(ci.body);
}

void Elaborator::ValidateAssignInExprRestrictions(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      for (const auto& ev : item->sensitivity) {
        WalkExprForAssignInExpr(ev.signal, true);
      }
      if (item->body) WalkStmtsForAssignInExpr(item->body);
    }
    if (item->kind == ModuleItemKind::kInitialBlock && item->body) {
      WalkStmtsForAssignInExpr(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForAssignInExpr(item->assign_rhs, true);
    }
  }
}

static std::string_view AliasNetIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

static bool ExprContainsHierarchicalRef(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (ExprContainsHierarchicalRef(e->lhs)) return true;
  if (ExprContainsHierarchicalRef(e->rhs)) return true;
  if (ExprContainsHierarchicalRef(e->base)) return true;
  for (auto* elem : e->elements) {
    if (ExprContainsHierarchicalRef(elem)) return true;
  }
  return false;
}

namespace {

void CheckAliasSelfAlias(const ModuleItem* item, DiagEngine& diag) {
  std::unordered_set<std::string_view> seen;
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!seen.insert(name).second) {
      diag.Error(item->loc, std::format("net '{}' aliased to itself", name),
                 Subclause::Unread());
    }
  }
}

void CheckAliasOperandKinds(
    const ModuleItem* item, DiagEngine& diag,
    const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& declared_names) {
  for (auto* net : item->alias_nets) {
    if (ExprContainsHierarchicalRef(net)) {
      diag.Error(item->loc,
                 "hierarchical references cannot be used in alias statements",
                 Subclause::Unread());
    }
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!net_names.count(name) && declared_names.count(name)) {
      diag.Error(item->loc,
                 std::format("'{}' is a variable, not a net; "
                             "variables cannot appear in alias statements",
                             name),
                 Subclause::Unread());
    }
  }
}

std::vector<std::string_view> CollectAliasNetNames(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& net_names) {
  std::vector<std::string_view> ident_names;
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (!name.empty() && net_names.count(name)) ident_names.push_back(name);
  }
  return ident_names;
}

void CheckAliasNetTypeCompat(
    const ModuleItem* item, DiagEngine& diag,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    const std::vector<std::string_view>& ident_names) {
  if (ident_names.size() < 2) return;
  auto first_type_it = var_types.find(ident_names[0]);
  NetType first_net_type = NetType::kWire;
  if (first_type_it != var_types.end())
    first_net_type = DataTypeToNetType(first_type_it->second);
  for (size_t i = 1; i < ident_names.size(); ++i) {
    NetType cur_net_type = NetType::kWire;
    auto cur_type_it = var_types.find(ident_names[i]);
    if (cur_type_it != var_types.end())
      cur_net_type = DataTypeToNetType(cur_type_it->second);
    if (cur_net_type != first_net_type) {
      diag.Error(item->loc,
                 std::format("nets in alias statement have incompatible types; "
                             "'{}' and '{}' are different net types",
                             ident_names[0], ident_names[i]),
                 Subclause::Unread());
      break;
    }
  }
}

template <typename ScopeFn>
void CheckAliasNetWidthCompat(const ModuleItem* item, DiagEngine& diag,
                              RtlirModule* mod,
                              const std::vector<std::string_view>& ident_names,
                              ScopeFn scope) {
  if (ident_names.size() < 2) return;
  auto scoped_first = scope(ident_names[0]);
  uint32_t first_width = 0;
  for (const auto& n : mod->nets) {
    if (n.name == scoped_first) {
      first_width = n.width;
      break;
    }
  }
  for (size_t i = 1; i < ident_names.size(); ++i) {
    auto scoped = scope(ident_names[i]);
    uint32_t w = 0;
    for (const auto& n : mod->nets) {
      if (n.name == scoped) {
        w = n.width;
        break;
      }
    }
    if (w != first_width) {
      diag.Error(item->loc,
                 std::format("nets in alias statement have different widths; "
                             "'{}' has width {} but '{}' has width {}",
                             ident_names[0], first_width, ident_names[i], w),
                 Subclause::Unread());
      break;
    }
  }
}

// §10.11: one constituent bit of an alias operand -- the (raw, same-scope) net
// name and the bit index within it. Raw names are used (not scoped) so the
// reference stays valid for the module-lifetime duplicate set and so that two
// statements naming the same net in the same scope compare equal.
using AliasBitRef = std::pair<std::string_view, uint32_t>;

// MSB-first bits of a plain net identifier, or nullopt for an unknown net.
template <typename WidthFn>
std::optional<std::vector<AliasBitRef>> FlattenAliasIdentBits(
    const Expr* e, WidthFn net_width) {
  uint32_t w = net_width(e->text);
  if (w == 0) return std::nullopt;
  std::vector<AliasBitRef> bits;
  for (uint32_t i = w; i-- > 0;) bits.emplace_back(e->text, i);
  return bits;
}

// MSB-first bits of a constant bit-select or part-select over a known net, or
// nullopt for a non-constant index, an indexed (+:/-:) select, or unknown net.
template <typename WidthFn>
std::optional<std::vector<AliasBitRef>> FlattenAliasSelectBits(
    const Expr* e, WidthFn net_width, const ScopeMap& scope) {
  bool indexed = e->is_part_select_plus || e->is_part_select_minus;
  if (!e->base || e->base->kind != ExprKind::kIdentifier || indexed)
    return std::nullopt;
  if (net_width(e->base->text) == 0) return std::nullopt;
  // §11.2.1: a constant_select bound may be a literal or a
  // parameter/localparam. Resolve against the module's parameter scope so a
  // parameter-based index is flattened to the same bits a literal would be --
  // otherwise the bit-level self/duplicate checks would silently skip a
  // parameterized select.
  auto hi = ConstEvalInt(e->index, scope);
  if (!hi) return std::nullopt;
  std::vector<AliasBitRef> bits;
  if (!e->index_end) {
    bits.emplace_back(e->base->text, static_cast<uint32_t>(*hi));
    return bits;
  }
  auto lo = ConstEvalInt(e->index_end, scope);
  if (!lo) return std::nullopt;
  int64_t a = *hi;
  int64_t b = *lo;
  if (a < b) std::swap(a, b);
  for (int64_t i = a; i >= b; --i)
    bits.emplace_back(e->base->text, static_cast<uint32_t>(i));
  return bits;
}

// Flatten an alias operand (identifier, constant bit/part-select, or
// concatenation of these) into its MSB-first list of constituent net bits.
// Returns nullopt if any part is not a constant select over a known net, so the
// caller skips the bit-level analysis rather than mis-reporting.
template <typename WidthFn>
std::optional<std::vector<AliasBitRef>> FlattenAliasOperandBits(
    const Expr* e, WidthFn net_width, const ScopeMap& scope) {
  if (!e) return std::nullopt;
  if (e->kind == ExprKind::kIdentifier)
    return FlattenAliasIdentBits(e, net_width);
  if (e->kind == ExprKind::kSelect)
    return FlattenAliasSelectBits(e, net_width, scope);
  if (e->kind != ExprKind::kConcatenation || e->repeat_count)
    return std::nullopt;
  std::vector<AliasBitRef> bits;
  for (auto* el : e->elements) {
    auto sub = FlattenAliasOperandBits(el, net_width, scope);
    if (!sub) return std::nullopt;
    bits.insert(bits.end(), sub->begin(), sub->end());
  }
  return bits;
}

// §10.11: an alias statement shall not alias a net bit to itself. When two
// operands of one statement place the same physical net bit at the same
// position, that bit is being aliased to itself (e.g.
// alias bus16 = {high12, bus16[3:0]} = {bus16[15:12], low12}). The whole-net
// form (alias a = a) is caught by CheckAliasSelfAlias; this covers the
// bit-level form that only surfaces through selects and concatenations.
bool AliasOperandsAliasBitToSelf(
    const std::vector<std::vector<AliasBitRef>>& operands, size_t width) {
  for (size_t i = 0; i < operands.size(); ++i) {
    for (size_t j = i + 1; j < operands.size(); ++j) {
      for (size_t p = 0; p < width; ++p) {
        if (operands[i][p] == operands[j][p]) return true;
      }
    }
  }
  return false;
}

// Scans every pair of operands position-by-position, inserting each canonical
// bit correspondence into the module-lifetime set; returns true on the first
// correspondence already present (i.e. specified more than once, §10.11).
bool AliasOperandsHaveDuplicateBit(
    const std::vector<std::vector<AliasBitRef>>& operands, size_t width,
    std::set<std::pair<AliasBitRef, AliasBitRef>>& seen) {
  for (size_t i = 0; i < operands.size(); ++i) {
    for (size_t j = i + 1; j < operands.size(); ++j) {
      for (size_t p = 0; p < width; ++p) {
        AliasBitRef a = operands[i][p];
        AliasBitRef b = operands[j][p];
        auto pair = (a <= b) ? std::make_pair(a, b) : std::make_pair(b, a);
        if (!seen.insert(pair).second) return true;
      }
    }
  }
  return false;
}

bool AliasHasStructuredOperand(const ModuleItem* item) {
  for (auto* net : item->alias_nets)
    if (net && net->kind != ExprKind::kIdentifier) return true;
  return false;
}

// §10.11: what an alias statement's operands are expanded against -- the module
// whose nets they name, the mapping from a bare name to its scoped form, and
// the constant scope a select bound folds in.
template <typename ScopeFn>
struct AliasExpansionCtx {
  RtlirModule* mod;
  ScopeFn scope;
  const ScopeMap& param_scope;
};

// Expand an alias statement's operands to equal-length bit-level vectors, or
// nullopt when it has no structured operand, a width is unknown, or the
// operands disagree on width (the latter is reported elsewhere).
template <typename ScopeFn>
std::optional<std::vector<std::vector<AliasBitRef>>> BuildAliasOperandBits(
    const ModuleItem* item, const AliasExpansionCtx<ScopeFn>& ctx) {
  if (!AliasHasStructuredOperand(item)) return std::nullopt;

  auto net_width = [&](std::string_view raw) -> uint32_t {
    auto scoped = ctx.scope(raw);
    for (const auto& n : ctx.mod->nets)
      if (n.name == scoped) return n.width;
    return 0;
  };

  std::vector<std::vector<AliasBitRef>> operands;
  for (auto* net : item->alias_nets) {
    auto flat = FlattenAliasOperandBits(net, net_width, ctx.param_scope);
    if (!flat) return std::nullopt;
    operands.push_back(std::move(*flat));
  }
  if (operands.size() < 2) return std::nullopt;
  size_t width = operands[0].size();
  for (const auto& op : operands)
    if (op.size() != width) return std::nullopt;
  return operands;
}

// §10.11: each member of an alias list shall be the same size. Whole-net pairs
// are handled by CheckAliasNetWidthCompat; this covers the structured case,
// where a select or concatenation operand can disagree in total width with the
// other members. Only compared when every operand flattens to a known,
// constant-bounded bit count -- an unknown net or non-constant select is left
// to the checks that already skip it, so no false width error is raised.
template <typename ScopeFn>
void CheckAliasStructuredWidthCompat(const ModuleItem* item, DiagEngine& diag,
                                     RtlirModule* mod, ScopeFn scope,
                                     const ScopeMap& param_scope) {
  if (!AliasHasStructuredOperand(item)) return;
  auto net_width = [&](std::string_view raw) -> uint32_t {
    auto scoped = scope(raw);
    for (const auto& n : mod->nets)
      if (n.name == scoped) return n.width;
    return 0;
  };
  std::optional<size_t> common;
  for (auto* net : item->alias_nets) {
    auto flat = FlattenAliasOperandBits(net, net_width, param_scope);
    if (!flat) return;
    if (!common) {
      common = flat->size();
    } else if (*common != flat->size()) {
      diag.Error(item->loc, "members of alias statement have different widths",
                 Subclause::Unread());
      return;
    }
  }
}

// §10.11: "it is not allowed to ... specify a given alias more than once." When
// an alias statement uses selects or concatenations, expand it to bit-level
// correspondences and flag a correspondence that was already established by an
// earlier alias statement. Whole-net identifier pairs are handled by
// CheckAliasDuplicatePairs, so this only engages structured operands.
template <typename ScopeFn>
void CheckAliasBitDuplicates(
    const ModuleItem* item, DiagEngine& diag,
    std::set<std::pair<AliasBitRef, AliasBitRef>>& seen,
    const AliasExpansionCtx<ScopeFn>& ctx) {
  auto operands = BuildAliasOperandBits(item, ctx);
  if (!operands) return;
  size_t width = (*operands)[0].size();
  if (AliasOperandsAliasBitToSelf(*operands, width)) {
    diag.Error(item->loc, "net bits aliased to themselves in alias statement",
               Subclause::Unread());
    return;
  }
  if (AliasOperandsHaveDuplicateBit(*operands, width, seen)) {
    diag.Error(item->loc, "alias bit correspondence specified more than once",
               Subclause::Unread());
  }
}

void CheckAliasDuplicatePairs(
    const ModuleItem* item, DiagEngine& diag,
    std::set<std::pair<std::string_view, std::string_view>>& alias_pairs,
    const std::vector<std::string_view>& ident_names) {
  for (size_t i = 0; i < ident_names.size(); ++i) {
    for (size_t j = i + 1; j < ident_names.size(); ++j) {
      auto a = ident_names[i];
      auto b = ident_names[j];
      auto pair = (a < b) ? std::make_pair(a, b) : std::make_pair(b, a);
      if (!alias_pairs.insert(pair).second) {
        diag.Error(item->loc,
                   std::format("alias between '{}' and '{}' "
                               "specified more than once",
                               a, b),
                   Subclause::Unread());
      }
    }
  }
}

}  // namespace

void Elaborator::ValidateAlias(const ModuleItem* item, RtlirModule* mod) {
  CheckAliasSelfAlias(item, diag_);
  CheckAliasOperandKinds(item, diag_, net_names_, declared_names_);
  std::vector<std::string_view> ident_names =
      CollectAliasNetNames(item, net_names_);
  CheckAliasNetTypeCompat(item, diag_, var_types_, ident_names);
  auto scoped = [this](std::string_view n) { return ScopedName(n); };
  CheckAliasNetWidthCompat(item, diag_, mod, ident_names, scoped);
  ScopeMap param_scope = BuildParamScope(mod);
  CheckAliasStructuredWidthCompat(item, diag_, mod, scoped, param_scope);
  CheckAliasDuplicatePairs(item, diag_, alias_pairs_, ident_names);
  CheckAliasBitDuplicates(item, diag_, alias_bit_pairs_,
                          AliasExpansionCtx{mod, scoped, param_scope});
}

void Elaborator::CheckAssocConcatTargetInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (!it->second.is_assoc) return;
  diag_.Error(s->rhs->range.start,
              "unpacked array concatenation cannot target an associative array",
              Subclause::Unread());
}

void Elaborator::WalkStmtsForAssocConcatTarget(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckAssocConcatTargetInAssign(s);
  }
  for (auto* sub : s->stmts) WalkStmtsForAssocConcatTarget(sub);
  WalkStmtsForAssocConcatTarget(s->then_branch);
  WalkStmtsForAssocConcatTarget(s->else_branch);
  WalkStmtsForAssocConcatTarget(s->body);
  WalkStmtsForAssocConcatTarget(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAssocConcatTarget(ci.body);
}

void Elaborator::ValidateAssocConcatTarget(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      WalkStmtsForAssocConcatTarget(item->body);
    }
  }
}

}  // namespace delta
