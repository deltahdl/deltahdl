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

// §7.8 with §26.3 and §8.23: the name the typedef table and the class-name set
// hold a type under where the unpacked dimension `dim` names it through a
// package or class scope, "p::idx_t" for `[p::idx_t]`; empty where `dim` is no
// scoped name.
std::string ScopedTypeKey(const Expr* dim);

// §7.8.5 (printed page 165): `real` and `shortreal`, and any type that holds
// one, are illegal as an associative array's index type. Reports, at `loc`,
// the first of the unpacked dimensions `dims` whose index type is such a type,
// a typedef name being judged by the type it stands for.
void CheckRealAssocIndexTypes(const std::vector<Expr*>& dims, SourceLoc loc,
                              const TypedefMap& typedefs, DiagEngine& diag);

// A.2.5 with §6.23: an index written as a type reference to an expression,
// `[type(k)]`, takes the type `resolve` gives that expression, kept where an
// index written as a data_type keeps its own, so ComputeUnpackedDims reads the
// two alike.
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
