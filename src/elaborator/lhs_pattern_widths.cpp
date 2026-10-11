#include <cstddef>
#include <cstdint>
#include <format>
#include <string_view>
#include <unordered_map>

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

// What a left-hand-side pattern's widths are read against: the module whose
// names its items and the right-hand side name, the module's typedefs and
// functions, and the scope a select's bounds fold in.
struct LhsPatternCtx {
  const RtlirModule* mod;
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, const ModuleItem*>& funcs;
  const ScopeMap& scope;
  DiagEngine& diag;
};

// Whether `name` names a variable or net of `mod` with no unpacked dimension,
// one whose select is a select of bits.
bool IsUnpackedFree(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables)
    if (v.name == name) return v.unpacked_size == 0;
  for (const auto& n : mod->nets)
    if (n.name == name) return n.num_unpacked_dims == 0;
  return false;
}

// The bit count of a pattern's right-hand side: a name's declared width, the
// span of a constant select of a vector, a call's declared return width, and
// otherwise what the operators give it. 0 where none of these is known.
uint32_t PatternRhsWidth(const Expr* rhs, const LhsPatternCtx& ctx) {
  if (rhs->kind == ExprKind::kIdentifier) return LookupLhsWidth(rhs, ctx.mod);
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

// §10.9 (printed page 261): each item of a typed pattern on the left-hand side
// has the bit count of the member of the pattern's type it stands for.
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

// §10.9 (printed page 260): a positional assignment pattern on the left-hand
// side of an assignment-like context holds the bits the right-hand side
// supplies, and an untyped one takes its type from the other side, which an
// untyped pattern there cannot give it. Fires on a bit count only when both
// sides have one, so that unrelated diagnostics keep their primacy.
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

// §10.9's rules reach an assignment wherever one is written: every statement
// of a process or a subroutine, and a continuous assignment.
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
  const LhsPatternCtx kCtx{mod, typedefs_, func_decls_, scope, diag_};
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      WalkStmtsForLhsPattern(item->body, kCtx);
    for (const Stmt* s : item->func_body_stmts) WalkStmtsForLhsPattern(s, kCtx);
    if (item->kind == ModuleItemKind::kContAssign)
      CheckLhsPattern(item->assign_lhs, item->assign_rhs, kCtx);
  }
}

}  // namespace delta
