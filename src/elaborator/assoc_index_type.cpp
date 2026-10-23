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

// Whether one struct/union member is, or holds, a real type. A member written
// through a typedef only reveals a real after the alias is resolved, so a named
// member type is followed into the typedef table -- under its "q::name" key
// where the member was written as `q::real_holder_t r`, since §26.3 (printed
// page 808) reaches q's declaration through the qualifier and a bare lookup
// found whatever an import of another package made `real_holder_t` stand for,
// so q's real went unseen or another package's real-free structure was
// reported; an inline nested struct/union member carries its full type in
// nested_type instead, and a real buried in that inline aggregate counts the
// same.
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
  // Guard against a pathological recursive typedef chain; a legitimate type
  // nests only a handful of levels deep.
  if (depth > 16) return false;
  if (dtype.kind == DataTypeKind::kNamed) {
    // A typedef of a qualified name, `typedef q::real_holder_t idx_t`, is
    // followed under its qualifier for the same reason as a member.
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

// Whether the unpacked dimension `dim` is an associative one whose index type
// is, or holds, a real: the parser keeps an index type as the identifier of the
// keyword or the name written, a name written through a package or class
// scope as the scope resolution it is, and any other type as a type reference.
static bool IsRealIndexType(const Expr* dim, const TypedefMap& typedefs) {
  if (dim == nullptr) return false;
  // A.2.5 with §6.23: an index written as a data_type or a type reference
  // carries its type, the parser's for a data_type and the elaborator's for
  // `type(expression)`. Every declaration this is asked of has had its
  // references resolved first: a module's variables and typedefs where they
  // are elaborated, its ports in ResolvePortTypeRefs, and every other
  // declaration in the walks of type_ref_walks.cpp.
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
