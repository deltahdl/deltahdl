#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <set>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/net_data_type.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

void ElaboratorOperationRules::WalkExprForCast(const Expr* expr) {
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

void ElaboratorOperationRules::WalkStmtsForCast(const Stmt* s) {
  if (!s) return;
  WalkExprForCast(s->rhs);
  WalkExprForCast(s->lhs);
  WalkExprForCast(s->expr);
  WalkExprForCast(s->condition);
  WalkExprForCast(s->assert_expr);
  // §6.24 states when a cast is legal -- §6.24.1 requires a positive size
  // and an integral operand -- and names no statement a cast written inside it
  // is exempt in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names none itself. It wrote out
  // six of the thirteen, so `fork r = signed'(2.5); join` and
  // `assert (ok) else r = signed'(2.5);` each carried a cast CheckCastExpr
  // never saw.
  ForEachChildStmt(s, [this](Stmt* const& sub) { WalkStmtsForCast(sub); });
}

void ElaboratorOperationRules::ValidateCastOperations(const ModuleDecl* decl) {
  cast_unpacked_structs_ = UnpackedStructVars(decl, typedefs_);
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
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

void ElaboratorOperationRules::WalkExprForAssignInExpr(const Expr* expr,
                                                       bool in_event_or_cont) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary && IsAssignOp(expr->op)) {
    if (in_event_or_cont) {
      diag_.Error(expr->range.start,
                  "assignment operator within expression is illegal in "
                  "this context",
                  Subclause("11.3.6"));
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

void ElaboratorOperationRules::WalkStmtsForAssignInExpr(const Stmt* s) {
  if (!s) return;

  if (s->kind == StmtKind::kAssign && s->rhs) {
    WalkExprForAssignInExpr(s->rhs, true);
  }
  // §11.3.6 names the event expression without regard to where the event
  // control stands: as a statement, `@((a = b)) ...`, or within an assignment,
  // `c = @((a = b)) 2`, whose events the statement holds as its own.
  for (const EventExpr& ev : s->events) {
    WalkExprForAssignInExpr(ev.signal, true);
    WalkExprForAssignInExpr(ev.iff_condition, true);
  }
  // §11.3.6 bars an assignment operator from an event expression, from an
  // expression in a procedural continuous assignment and from any expression
  // outside a procedural statement, and names no statement the procedural
  // continuous assignment may stand in to escape that, so this descends every
  // link ForEachChildStmt in elaborator_validate_internal.h names and names
  // none itself. It wrote out six of the thirteen, so
  // `fork assign c = (a = b); join` and
  // `randcase 1: assign c = (a = b); endcase` each held an embedded assignment
  // operator that was never looked at.
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { WalkStmtsForAssignInExpr(sub); });
}

void ElaboratorOperationRules::ValidateAssignInExprRestrictions(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      for (const auto& ev : item->sensitivity) {
        WalkExprForAssignInExpr(ev.signal, true);
      }
      if (item->body) WalkStmtsForAssignInExpr(item->body);
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

// §10.11 Syntax 10-6: a select in an alias operand is a constant_select, so
// every index and bound along it, down to the net it is taken from, folds.
bool IsAliasConstantSelect(const Expr* e, const ScopeMap& scope) {
  for (; e->kind == ExprKind::kSelect; e = e->base) {
    if (!ConstEvalInt(e->index, scope)) return false;
    if (e->index_end && !ConstEvalInt(e->index_end, scope)) return false;
  }
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess;
}

// §10.11 Syntax 10-6: an alias operand is a net_lvalue -- a net named with a
// constant select, a concatenation of net_lvalues, or a positional assignment
// pattern of them with or without a type. A member access stands here for the
// hierarchical name CheckAliasOperandKinds reports.
bool IsAliasNetLvalue(const Expr* e, const ScopeMap& scope) {
  switch (e->kind) {
    case ExprKind::kIdentifier:
    case ExprKind::kMemberAccess:
      return true;
    case ExprKind::kSelect:
      return IsAliasConstantSelect(e, scope);
    case ExprKind::kCast:
      return e->lhs->kind == ExprKind::kAssignmentPattern &&
             IsAliasNetLvalue(e->lhs, scope);
    case ExprKind::kAssignmentPattern:
      if (!e->pattern_keys.empty()) return false;
      [[fallthrough]];
    case ExprKind::kConcatenation:
      for (const Expr* el : e->elements)
        if (!IsAliasNetLvalue(el, scope)) return false;
      return true;
    default:
      return false;
  }
}

// Reports each operand that is no net_lvalue and answers whether all are, so
// the checks that read an operand's nets and bits see only the forms
// Syntax 10-6 gives.
bool CheckAliasOperandForms(const ModuleItem* item, DiagEngine& diag,
                            const ScopeMap& scope) {
  bool all = true;
  for (const Expr* net : item->alias_nets) {
    if (IsAliasNetLvalue(net, scope)) continue;
    diag.Error(item->loc,
               "alias operand is not a net_lvalue: a net with constant "
               "selects, or a concatenation or pattern of these",
               Subclause("10.11"));
    all = false;
  }
  return all;
}

// The names an alias operand reaches: the net each select is taken from, and
// every name a concatenation or a pattern holds.
void CollectAliasLeafNames(const Expr* e, std::vector<std::string_view>& out) {
  while (e->kind == ExprKind::kSelect) e = e->base;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  if (e->kind == ExprKind::kCast) e = e->lhs;
  for (const Expr* el : e->elements) CollectAliasLeafNames(el, out);
}

void CheckAliasSelfAlias(const ModuleItem* item, DiagEngine& diag) {
  std::unordered_set<std::string_view> seen;
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!seen.insert(name).second) {
      diag.Error(item->loc, std::format("net '{}' aliased to itself", name),
                 Subclause("10.11"));
    }
  }
}

// §10.11: neither a hierarchical reference nor a variable may appear in an
// alias statement, whether as a whole operand or as the net a select or a
// concatenation element names.
void CheckAliasOperandKinds(
    const ModuleItem* item, DiagEngine& diag,
    const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& declared_names,
    const std::vector<std::string_view>& leaves) {
  for (auto* net : item->alias_nets) {
    if (ExprContainsHierarchicalRef(net)) {
      diag.Error(item->loc,
                 "hierarchical references cannot be used in alias statements",
                 Subclause("10.11"));
    }
  }
  for (std::string_view name : leaves) {
    if (!net_names.count(name) && declared_names.count(name)) {
      diag.Error(item->loc,
                 std::format("'{}' is a variable, not a net; "
                             "variables cannot appear in alias statements",
                             name),
                 Subclause("10.11"));
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

const RtlirNet* FindAliasNet(const RtlirModule* mod, std::string_view scoped) {
  for (const auto& n : mod->nets)
    if (n.name == scoped) return &n;
  return nullptr;
}

// §10.11: the nets an alias statement connects are of one net type, the
// keyword each declaration wrote or the default it took, whatever their data
// types; a select or a concatenation element counts as the net it names.
template <typename ScopeFn>
void CheckAliasNetTypeCompat(const ModuleItem* item, DiagEngine& diag,
                             const RtlirModule* mod,
                             const std::vector<std::string_view>& leaves,
                             ScopeFn scope) {
  std::string_view first_name;
  const RtlirNet* first = nullptr;
  for (std::string_view name : leaves) {
    const RtlirNet* net = FindAliasNet(mod, scope(name));
    if (!net) continue;
    if (!first) {
      first = net;
      first_name = name;
    } else if (net->net_type != first->net_type) {
      diag.Error(item->loc,
                 std::format("nets in alias statement have incompatible types; "
                             "'{}' and '{}' are different net types",
                             first_name, name),
                 Subclause("10.11"));
      return;
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
                 Subclause("10.11"));
      break;
    }
  }
}

// §10.11: one constituent bit of an alias operand -- the net, by the name its
// scope gives it, and the bit's offset above the net's least significant end.
// The scoped name tells one generate iteration's net from another's, and the
// offset is the one measure a whole name and a select agree on, whichever way
// the net's range runs and wherever it starts.
using AliasBitRef = std::pair<std::string_view, uint32_t>;

// §10.11: what an alias statement's operands are expanded against -- the module
// whose nets they name, the mapping from a bare name to its scoped form, and
// the constant scope a select bound folds in.
template <typename ScopeFn>
struct AliasExpansionCtx {
  RtlirModule* mod;
  ScopeFn scope;
  const ScopeMap& param_scope;
};

// MSB-first bits of a plain net identifier, or nullopt for an unknown net.
template <typename ScopeFn>
std::optional<std::vector<AliasBitRef>> FlattenAliasIdentBits(
    const Expr* e, const AliasExpansionCtx<ScopeFn>& ctx) {
  std::string_view scoped = ctx.scope(e->text);
  const RtlirNet* net = FindAliasNet(ctx.mod, scoped);
  if (!net) return std::nullopt;
  std::vector<AliasBitRef> bits;
  for (uint32_t i = net->width; i-- > 0;) bits.emplace_back(scoped, i);
  return bits;
}

// MSB-first bits of a constant bit-select or part-select over a known net, each
// index resolved against the range the net declared, or nullopt for an indexed
// (+:/-:) select, a select of a select, or an unknown net.
template <typename ScopeFn>
std::optional<std::vector<AliasBitRef>> FlattenAliasSelectBits(
    const Expr* e, const AliasExpansionCtx<ScopeFn>& ctx) {
  bool indexed = e->is_part_select_plus || e->is_part_select_minus;
  if (e->base->kind != ExprKind::kIdentifier || indexed) return std::nullopt;
  std::string_view scoped = ctx.scope(e->base->text);
  if (!FindAliasNet(ctx.mod, scoped)) return std::nullopt;
  // §11.2.1: a constant_select bound may be a literal or a parameter, and
  // IsAliasConstantSelect has already folded each one in this scope. §11.5.1
  // has a part-select's first index address its more significant end, which
  // lies at the higher offset whichever way the net's range runs.
  PackedRange range = SignalDeclaredRange(scoped, ctx.mod, ctx.param_scope);
  int64_t hi =
      range.OffsetOf(ConstEvalInt(e->index, ctx.param_scope).value_or(0));
  int64_t lo = hi;
  if (e->index_end)
    lo =
        range.OffsetOf(ConstEvalInt(e->index_end, ctx.param_scope).value_or(0));
  std::vector<AliasBitRef> bits;
  for (int64_t i = hi; i >= lo; --i)
    bits.emplace_back(scoped, static_cast<uint32_t>(i));
  return bits;
}

// Flatten an alias operand (identifier, constant bit/part-select, or
// concatenation or positional pattern of these) into its MSB-first list of
// constituent net bits. Syntax 10-6 has a pattern, typed or not, stand for its
// items' bits in order, as a concatenation does; CheckAliasOperandForms has
// already made a cast here one that types a positional pattern. Returns
// nullopt if any part is not a constant select over a known net, so the caller
// skips the bit-level analysis rather than mis-reporting.
template <typename ScopeFn>
std::optional<std::vector<AliasBitRef>> FlattenAliasOperandBits(
    const Expr* e, const AliasExpansionCtx<ScopeFn>& ctx) {
  if (e->kind == ExprKind::kIdentifier) return FlattenAliasIdentBits(e, ctx);
  if (e->kind == ExprKind::kSelect) return FlattenAliasSelectBits(e, ctx);
  if (e->kind == ExprKind::kCast) e = e->lhs;
  if (e->kind != ExprKind::kConcatenation &&
      e->kind != ExprKind::kAssignmentPattern) {
    return std::nullopt;
  }
  std::vector<AliasBitRef> bits;
  for (auto* el : e->elements) {
    auto sub = FlattenAliasOperandBits(el, ctx);
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
// bit correspondence into the module-lifetime set; answers the first pair of
// operands holding a correspondence already present (i.e. specified more than
// once, §10.11).
std::optional<std::pair<size_t, size_t>> AliasOperandsHaveDuplicateBit(
    const std::vector<std::vector<AliasBitRef>>& operands, size_t width,
    std::set<std::pair<AliasBitRef, AliasBitRef>>& seen) {
  for (size_t i = 0; i < operands.size(); ++i) {
    for (size_t j = i + 1; j < operands.size(); ++j) {
      for (size_t p = 0; p < width; ++p) {
        AliasBitRef a = operands[i][p];
        AliasBitRef b = operands[j][p];
        auto pair = (a <= b) ? std::make_pair(a, b) : std::make_pair(b, a);
        if (!seen.insert(pair).second) return std::make_pair(i, j);
      }
    }
  }
  return std::nullopt;
}

bool AliasHasStructuredOperand(const ModuleItem* item) {
  for (auto* net : item->alias_nets)
    if (net->kind != ExprKind::kIdentifier) return true;
  return false;
}

// Expand an alias statement's operands to equal-length bit-level vectors, or
// nullopt when a width is unknown or the operands disagree on width (the
// latter is reported elsewhere).
template <typename ScopeFn>
std::optional<std::vector<std::vector<AliasBitRef>>> BuildAliasOperandBits(
    const ModuleItem* item, const AliasExpansionCtx<ScopeFn>& ctx) {
  std::vector<std::vector<AliasBitRef>> operands;
  for (auto* net : item->alias_nets) {
    auto flat = FlattenAliasOperandBits(net, ctx);
    if (!flat) return std::nullopt;
    operands.push_back(std::move(*flat));
  }
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
                                     const AliasExpansionCtx<ScopeFn>& ctx) {
  if (!AliasHasStructuredOperand(item)) return;
  std::optional<size_t> common;
  for (auto* net : item->alias_nets) {
    auto flat = FlattenAliasOperandBits(net, ctx);
    if (!flat) return;
    if (!common) {
      common = flat->size();
    } else if (*common != flat->size()) {
      diag.Error(item->loc, "members of alias statement have different widths",
                 Subclause("10.11"));
      return;
    }
  }
}

// §10.11: no alias may be specified more than once, whether it is written with
// whole nets, selects or concatenations, so every statement is expanded to
// bit-level correspondences and checked against those of the statements
// before it. A statement of whole nets alone names the two nets its repeat
// joins; one with a select or a concatenation is reported by its bits, and
// is the only form a bit can be aliased to itself without a net repeating.
template <typename ScopeFn>
void CheckAliasBitDuplicates(
    const ModuleItem* item, DiagEngine& diag,
    std::set<std::pair<AliasBitRef, AliasBitRef>>& seen,
    const AliasExpansionCtx<ScopeFn>& ctx) {
  auto operands = BuildAliasOperandBits(item, ctx);
  if (!operands) return;
  size_t width = (*operands)[0].size();
  bool structured = AliasHasStructuredOperand(item);
  if (structured && AliasOperandsAliasBitToSelf(*operands, width)) {
    diag.Error(item->loc, "net bits aliased to themselves in alias statement",
               Subclause("10.11"));
    return;
  }
  auto repeat = AliasOperandsHaveDuplicateBit(*operands, width, seen);
  if (!repeat) return;
  if (structured) {
    diag.Error(item->loc, "alias bit correspondence specified more than once",
               Subclause("10.11"));
    return;
  }
  diag.Error(item->loc,
             std::format("alias between '{}' and '{}' specified more than once",
                         item->alias_nets[repeat->first]->text,
                         item->alias_nets[repeat->second]->text),
             Subclause("10.11"));
}

// §10.11: an alias operand in a generate block names the net of the innermost
// enclosing scope that declares it, which may be the module itself, so a name
// is tried under each block prefix from the innermost out before bare.
std::string_view ResolveAliasNetScope(
    std::string_view raw, const RtlirModule* mod,
    const std::vector<std::string_view>& prefixes) {
  for (auto it = prefixes.rbegin(); it != prefixes.rend(); ++it) {
    for (const auto& n : mod->nets) {
      if (n.name.size() == it->size() + raw.size() && n.name.starts_with(*it) &&
          n.name.ends_with(raw))
        return n.name;
    }
  }
  return raw;
}

}  // namespace

void Elaborator::ValidateAlias(const ModuleItem* item, RtlirModule* mod) {
  // §11.2.1 with §27.4: a select bound may name a parameter, or the genvar of
  // the loop generate block the statement stands in.
  ScopeMap param_scope = BuildParamScope(mod);
  for (const auto& [name, value] : gen_const_scope_) param_scope[name] = value;
  if (!CheckAliasOperandForms(item, diag_, param_scope)) return;
  std::vector<std::string_view> leaves;
  for (const Expr* net : item->alias_nets) CollectAliasLeafNames(net, leaves);
  auto scoped = [this, mod](std::string_view n) {
    return ResolveAliasNetScope(n, mod, gen_prefix_scopes_);
  };
  CheckAliasSelfAlias(item, diag_);
  CheckAliasOperandKinds(item, diag_, net_names_, declared_names_, leaves);
  CheckAliasNetTypeCompat(item, diag_, mod, leaves, scoped);
  CheckAliasNetWidthCompat(item, diag_, mod,
                           CollectAliasNetNames(item, net_names_), scoped);
  const AliasExpansionCtx kCtx{mod, scoped, param_scope};
  CheckAliasStructuredWidthCompat(item, diag_, kCtx);
  CheckAliasBitDuplicates(item, diag_, alias_bit_pairs_, kCtx);
}

void ElaboratorOperationRules::CheckAssocConcatTargetInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (!it->second.is_assoc) return;
  diag_.Error(s->rhs->range.start,
              "unpacked array concatenation cannot target an associative array",
              Subclause("10.10"));
}

// §7.8: whether unpacked dimensions `dims` make an associative array, the
// first being an index type rather than a size, `[]` or a queue's `[$]`.
bool ElaboratorOperationRules::DeclaresAssocArray(
    const std::vector<Expr*>& dims) const {
  if (dims.empty() || dims[0] == nullptr || IsQueueDim(dims[0])) return false;
  const TypeShapeTables kTables{typedefs_, td_array_dims_, class_names_};
  return !IsFixedSizeUnpackedDim(dims[0], kTables);
}

// §10.10 (printed page 264): an associative array is no target of an unpacked
// array concatenation, initialized by one in its declaration as much as
// assigned one.
void ElaboratorOperationRules::CheckAssocConcatInit(
    const Expr* init, const std::vector<Expr*>& dims) {
  if (init == nullptr || init->kind != ExprKind::kConcatenation) return;
  if (!DeclaresAssocArray(dims)) return;
  diag_.Error(init->range.start,
              "unpacked array concatenation cannot target an associative array",
              Subclause("10.10"));
}

void ElaboratorOperationRules::WalkStmtsForAssocConcatTarget(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckAssocConcatTargetInAssign(s);
  }
  if (s->kind == StmtKind::kVarDecl)
    CheckAssocConcatInit(s->var_init, s->var_unpacked_dims);
  // §10.10 requires the target of an unpacked array concatenation to be an
  // array whose slowest-varying dimension is unpacked fixed-size, queue or
  // dynamic, and makes a target of any other type, an associative array
  // included, illegal. It names no statement the assignment may be written in
  // to escape that, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names none itself. It wrote out
  // six of the thirteen, so `fork aa = {1, 2, 3}; join` and
  // `for (aa = {1, 2, 3}; i < 1; i = i + 1)` each targeted an associative array
  // with a concatenation that CheckAssocConcatTargetInAssign never saw.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForAssocConcatTarget(sub); });
}

void ElaboratorOperationRules::ValidateAssocConcatTarget(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkStmtsForAssocConcatTarget(item->body);
    }
    if (item->kind == ModuleItemKind::kVarDecl)
      CheckAssocConcatInit(item->init_expr, item->unpacked_dims);
  }
}

}  // namespace delta
