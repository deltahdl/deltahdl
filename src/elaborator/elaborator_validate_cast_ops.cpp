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

  if (s->kind == StmtKind::kAssign || s->kind == StmtKind::kForce) {
    WalkExprForAssignInExpr(s->rhs, true);
  }
  for (const EventExpr& ev : s->events) {
    WalkExprForAssignInExpr(ev.signal, true);
    WalkExprForAssignInExpr(ev.iff_condition, true);
  }
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
    WalkExprForAssignInExpr(item->init_expr, true);
    for (const auto& conn : item->inst_ports)
      WalkExprForAssignInExpr(conn.second, true);
  }
  for (const auto& param : decl->params)
    WalkExprForAssignInExpr(param.second, true);
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

bool IsAliasConstantSelect(const Expr* e, const ScopeMap& scope) {
  for (; e->kind == ExprKind::kSelect; e = e->base) {
    if (!ConstEvalInt(e->index, scope)) return false;
    if (e->index_end && !ConstEvalInt(e->index_end, scope)) return false;
  }
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess;
}

bool IsAliasNetLvalue(const Expr* e, const ScopeMap& scope) {
  if (e->is_parenthesized) return false;
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

using AliasBitRef = std::pair<std::string_view, uint32_t>;

template <typename ScopeFn>
struct AliasExpansionCtx {
  RtlirModule* mod;
  ScopeFn scope;
  const ScopeMap& param_scope;
};

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

template <typename ScopeFn>
std::optional<std::vector<AliasBitRef>> FlattenAliasSelectBits(
    const Expr* e, const AliasExpansionCtx<ScopeFn>& ctx) {
  bool indexed = e->is_part_select_plus || e->is_part_select_minus;
  if (e->base->kind != ExprKind::kIdentifier || indexed) return std::nullopt;
  std::string_view scoped = ctx.scope(e->base->text);
  if (!FindAliasNet(ctx.mod, scoped)) return std::nullopt;
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

bool ElaboratorOperationRules::DeclaresAssocArray(
    const std::vector<Expr*>& dims) const {
  if (dims.empty() || dims[0] == nullptr || IsQueueDim(dims[0])) return false;
  const TypeShapeTables kTables{typedefs_, td_array_dims_, class_names_};
  return !IsFixedSizeUnpackedDim(dims[0], kTables);
}

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
