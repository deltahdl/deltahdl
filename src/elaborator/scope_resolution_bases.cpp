#include "elaborator/scope_resolution_bases.h"

#include <algorithm>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

void CollectScopeBases(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->is_scope_resolution && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier && e->lhs->scope_prefix.empty() &&
      !e->lhs->text.starts_with("$")) {
    out.push_back(e);
  }
  CollectScopeBases(e->lhs, out);
  CollectScopeBases(e->rhs, out);
  CollectScopeBases(e->base, out);
  CollectScopeBases(e->index, out);
  CollectScopeBases(e->index_end, out);
  CollectScopeBases(e->condition, out);
  CollectScopeBases(e->true_expr, out);
  CollectScopeBases(e->false_expr, out);
  CollectScopeBases(e->repeat_count, out);
  CollectScopeBases(e->with_expr, out);
  CollectScopeBases(e->stream_range, out);
  for (const auto* a : e->args) CollectScopeBases(a, out);
  for (const auto* el : e->elements) CollectScopeBases(el, out);
}

static bool DeclaresBlockTypeName(const Stmt* s) {
  const ModuleItem* item = s->decl_item;
  if (item == nullptr) return false;
  return item->kind == ModuleItemKind::kTypedef ||
         (item->kind == ModuleItemKind::kParamDecl &&
          item->data_type.kind == DataTypeKind::kVoid);
}

static void CollectBlockScopeBases(const Stmt* s,
                                   std::vector<std::string_view> type_names,
                                   std::vector<const Expr*>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    std::vector<const Expr*> refs;
    CollectScopeBases(s->rhs, refs);
    for (const Expr* ref : refs) {
      if (std::ranges::find(type_names, ref->lhs->text) == type_names.end())
        out.push_back(ref);
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (sub != nullptr && DeclaresBlockTypeName(sub))
      type_names.push_back(sub->decl_item->name);
    CollectBlockScopeBases(sub, type_names, out);
  });
}

void CollectProcScopeBases(const Stmt* s, std::vector<const Expr*>& out) {
  CollectBlockScopeBases(s, {}, out);
}

}  // namespace delta
