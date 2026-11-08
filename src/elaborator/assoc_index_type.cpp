#include "elaborator/assoc_index_type.h"

#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

static bool ContainsRealType(const DataType& dtype, const TypedefMap& tds,
                             int depth = 0);

static bool StructMemberContainsRealType(const StructMember& m,
                                         const TypedefMap& tds, int depth) {
  if (IsRealType(m.type_kind)) return true;
  DataType named;
  named.kind = m.type_kind;
  named.type_name = m.type_name;
  named.scope_name = m.scope_name;
  const DataType* resolved = FindNamedType(named, tds);
  if (resolved != nullptr && ContainsRealType(*resolved, tds, depth + 1))
    return true;
  return m.nested_type != nullptr &&
         ContainsRealType(*m.nested_type, tds, depth + 1);
}

static bool ContainsRealType(const DataType& dtype, const TypedefMap& tds,
                             int depth) {
  if (depth > 16) return false;
  if (dtype.kind == DataTypeKind::kNamed) {
    const DataType* resolved = FindNamedType(dtype, tds);
    return resolved != nullptr && ContainsRealType(*resolved, tds, depth + 1);
  }
  if (IsRealType(dtype.kind)) return true;
  for (const auto& m : dtype.struct_members) {
    if (StructMemberContainsRealType(m, tds, depth)) return true;
  }
  return false;
}

std::string ScopedTypeKey(const Expr* dim) {
  if (dim->kind != ExprKind::kMemberAccess || !dim->is_scope_resolution) {
    return {};
  }
  return std::string(dim->lhs->text) + "::" + std::string(dim->rhs->text);
}

static bool IsRealIndexType(const Expr* dim, const TypedefMap& typedefs) {
  if (dim == nullptr) return false;
  if (dim->kind == ExprKind::kTypeRef) {
    return ContainsRealType(*dim->type_value, typedefs);
  }
  const std::string kName = dim->kind == ExprKind::kIdentifier
                                ? std::string(dim->text)
                                : ScopedTypeKey(dim);
  if (kName == "real" || kName == "shortreal" || kName == "realtime") {
    return true;
  }
  auto it = typedefs.find(kName);
  return it != typedefs.end() && ContainsRealType(it->second, typedefs);
}

void CheckRealAssocIndexTypes(const std::vector<Expr*>& dims, SourceLoc loc,
                              const TypedefMap& typedefs, DiagEngine& diag) {
  for (const Expr* dim : dims) {
    if (!IsRealIndexType(dim, typedefs)) continue;
    diag.Error(loc,
               "real or shortreal type shall not be used as an associative "
               "array index type",
               Subclause("7.8.5"));
    return;
  }
}

}  // namespace delta
