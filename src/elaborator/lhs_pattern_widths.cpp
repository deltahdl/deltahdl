#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <numeric>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct LhsPatternCtx {
  const RtlirModule* mod;
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, const ModuleItem*>& funcs;
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>& arrays;
  const ScopeMap& scope;
  DiagEngine& diag;
};

bool IsUnpackedFree(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables)
    if (v.name == name) return v.unpacked_size == 0;
  for (const auto& n : mod->nets)
    if (n.name == name) return n.num_unpacked_dims == 0;
  return false;
}

uint32_t ElementCount(std::string_view name, const LhsPatternCtx& ctx) {
  auto it = ctx.arrays.find(name);
  if (it == ctx.arrays.end()) return 1;
  const std::vector<uint32_t>& sizes = it->second.dim_sizes;
  if (sizes.size() != it->second.num_unpacked_dims) return 0;
  return std::accumulate(sizes.begin(), sizes.end(), 1U, std::multiplies<>());
}

uint32_t PatternRhsWidth(const Expr* rhs, const LhsPatternCtx& ctx) {
  if (rhs->kind == ExprKind::kIdentifier)
    return LookupLhsWidth(rhs, ctx.mod) * ElementCount(rhs->text, ctx);
  if (rhs->kind == ExprKind::kSelect &&
      rhs->base->kind == ExprKind::kIdentifier &&
      IsUnpackedFree(rhs->base->text, ctx.mod))
    return SelectLhsWidth(rhs, ctx.scope);
  if (rhs->kind == ExprKind::kCall) {
    auto it = ctx.funcs.find(rhs->callee);
    if (it == ctx.funcs.end()) return 0;
    return EvalTypeWidth(it->second->return_type, ctx.typedefs, ctx.scope);
  }
  return InferExprWidth(rhs, ctx.typedefs);
}

void CheckTypedLhsPatternItems(const Expr* cast, const LhsPatternCtx& ctx) {
  auto it = ctx.typedefs.find(cast->text);
  if (it == ctx.typedefs.end()) return;
  const auto& members = it->second.struct_members;
  const auto& items = cast->lhs->elements;
  for (size_t i = 0; i < items.size() && i < members.size(); ++i) {
    uint32_t item_w = LookupLhsWidth(items[i], ctx.mod);
    uint32_t member_w = EvalStructMemberWidth(members[i], ctx.typedefs);
    if (item_w == 0 || item_w == member_w) continue;
    ctx.diag.Error(items[i]->range.start,
                   std::format("LHS assignment pattern item has {} bits but "
                               "member '{}' of its type has {} bits",
                               item_w, members[i].name, member_w),
                   Subclause("10.9"));
  }
}

void CheckLhsPattern(const Expr* lhs, const Expr* rhs,
                     const LhsPatternCtx& ctx) {
  const Expr* pat = lhs;
  if (pat->kind == ExprKind::kCast) pat = pat->lhs;
  if (pat->kind != ExprKind::kAssignmentPattern) return;
  if (pat == lhs && rhs->kind == ExprKind::kAssignmentPattern) {
    ctx.diag.Error(lhs->range.start,
                   "an assignment between two untyped assignment patterns "
                   "gives neither a type",
                   Subclause("10.9"));
    return;
  }
  if (!pat->pattern_keys.empty() || pat->elements.empty()) return;
  if (pat != lhs) CheckTypedLhsPatternItems(lhs, ctx);
  uint32_t sum = 0;
  for (const auto* elem : pat->elements) {
    uint32_t w = LookupLhsWidth(elem, ctx.mod);
    if (w == 0) return;
    sum += w;
  }
  uint32_t rhs_w = PatternRhsWidth(rhs, ctx);
  if (rhs_w == 0 || sum == rhs_w) return;
  ctx.diag.Error(lhs->range.start,
                 std::format("LHS assignment pattern needs {} bits but RHS "
                             "supplies {} bits",
                             sum, rhs_w),
                 Subclause("10.9"));
}

void WalkStmtsForLhsPattern(const Stmt* s, const LhsPatternCtx& ctx) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckLhsPattern(s->lhs, s->rhs, ctx);
  }
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { WalkStmtsForLhsPattern(sub, ctx); });
}

}  // namespace

void Elaborator::ValidateLhsPatternWidths(const ModuleDecl* decl,
                                          const RtlirModule* mod) {
  ScopeMap scope = BuildParamScope(mod);
  const LhsPatternCtx kCtx{mod,   typedefs_, func_decls_, var_array_info_,
                           scope, diag_};
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      WalkStmtsForLhsPattern(item->body, kCtx);
    for (const Stmt* s : item->func_body_stmts) WalkStmtsForLhsPattern(s, kCtx);
    if (item->kind == ModuleItemKind::kContAssign)
      CheckLhsPattern(item->assign_lhs, item->assign_rhs, kCtx);
    if (item->kind != ModuleItemKind::kAlias) continue;
    for (const Expr* net : item->alias_nets)
      if (net->kind == ExprKind::kCast) CheckTypedLhsPatternItems(net, kCtx);
  }
}

}  // namespace delta
