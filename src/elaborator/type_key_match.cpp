#include "elaborator/type_key_match.h"

#include <string_view>
#include <tuple>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

bool IsTypeKey(std::string_view key, const TypedefMap& typedefs) {
  return IsTypeKeyword(key) || typedefs.count(key) != 0;
}

bool TypeKeyMatchesType(std::string_view key, const DataType& type,
                        const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* t = FollowTypedefs(type, typedefs, names);
  if (t == nullptr) return false;
  auto it = typedefs.find(key);
  if (it == typedefs.end())
    return TypeKeyMatchesKind(key, t->kind) && t->packed_dim_left == nullptr;
  const DataType* k = FollowTypedefs(it->second, typedefs, names);
  if (k == nullptr) return false;
  // §6.22.1 (c) and (d): an enum, structure or union matches only a type of
  // the same declaration.
  if (k->decl_loc.IsValid() || t->decl_loc.IsValid()) {
    return std::tie(k->decl_loc.file_id, k->decl_loc.line,
                    k->decl_loc.column) ==
           std::tie(t->decl_loc.file_id, t->decl_loc.line, t->decl_loc.column);
  }
  return k->kind == t->kind &&
         EvalTypeWidth(*k, typedefs) == EvalTypeWidth(*t, typedefs);
}

bool TypeKeyMatchesMember(std::string_view key, const StructMember& member,
                          const TypedefMap& typedefs) {
  if (!member.unpacked_dims.empty()) return false;
  if (member.nested_type != nullptr)
    return TypeKeyMatchesType(key, *member.nested_type, typedefs);
  DataType dt;
  dt.kind = member.type_kind;
  dt.type_name = member.type_name;
  dt.packed_dim_left = member.packed_dim_left;
  dt.packed_dim_right = member.packed_dim_right;
  dt.extra_packed_dims = member.extra_packed_dims;
  return TypeKeyMatchesType(key, dt, typedefs);
}

}  // namespace delta
