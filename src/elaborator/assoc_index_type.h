#pragma once

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

std::string ScopedTypeKey(const Expr* dim);

void CheckRealAssocIndexTypes(const std::vector<Expr*>& dims, SourceLoc loc,
                              const TypedefMap& typedefs, DiagEngine& diag);

template <typename Resolve>
void ResolveTypeRefIndexDims(const std::vector<Expr*>& dims, Resolve resolve,
                             Arena& arena) {
  for (Expr* dim : dims) {
    if (dim == nullptr || dim->kind != ExprKind::kTypeRef ||
        dim->type_value != nullptr) {
      continue;
    }
    DataType referenced;
    referenced.type_ref_expr = dim->lhs;
    resolve(referenced);
    dim->type_value = arena.Create<DataType>(referenced);
  }
}

}  // namespace delta
