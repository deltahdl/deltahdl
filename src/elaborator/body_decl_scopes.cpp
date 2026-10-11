#include <cstddef>
#include <functional>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

// A for-loop variable writes no unpacked dimension (A.6.8).
static const std::vector<Expr*> kNoUnpackedDims;

void BodyDeclScopes::DeclareFormal(const FunctionArg& arg) {
  decls_.push_back(
      {arg.name, &arg.data_type, &arg.unpacked_dims, default_auto_});
}

const BodyDeclScopes::Decl* BodyDeclScopes::Find(std::string_view name) const {
  for (auto it = decls_.rbegin(); it != decls_.rend(); ++it)
    if (it->name == name) return &*it;
  return nullptr;
}

void BodyDeclScopes::Walk(const Stmt* s,
                          const std::function<void(const Stmt*)>& visit) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    decls_.push_back(
        {s->var_name, &s->var_decl_type, &s->var_unpacked_dims,
         s->var_is_automatic || (default_auto_ && !s->var_is_static)});
  }
  visit(s);
  size_t mark = decls_.size();
  if (s->kind == StmtKind::kFor) {
    for (size_t i = 0; i < s->for_inits.size(); ++i) {
      if (s->for_init_types[i].kind == DataTypeKind::kImplicit) continue;
      decls_.push_back({ExprIdent(s->for_inits[i]->lhs), &s->for_init_types[i],
                        &kNoUnpackedDims, true});
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) { Walk(sub, visit); });
  if (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork ||
      s->kind == StmtKind::kFor)
    decls_.resize(mark);
}

}  // namespace delta
