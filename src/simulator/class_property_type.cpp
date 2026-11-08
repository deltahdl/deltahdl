#include <optional>
#include <string_view>

#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_class_params.h"

namespace delta {

static const DataType* ClassTypedefNamed(const ClassDecl* cls,
                                         std::string_view name) {
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kTypedef && m->name == name &&
        m->typedef_item != nullptr)
      return &m->typedef_item->typedef_type;
  }
  return nullptr;
}

static std::optional<DataType> NextAlong(const DataType& cur,
                                         const ClassDecl* cls,
                                         const TypedefMap& type_params) {
  if (!cur.scope_name.empty()) return ThroughBoundPrefix(cur, type_params);
  auto bound = type_params.find(cur.type_name);
  if (bound != type_params.end()) return bound->second;
  if (const DataType* td = ClassTypedefNamed(cls, cur.type_name)) return *td;
  return std::nullopt;
}

DataType ClassPropertyType(const DataType& type, const ClassDecl* cls,
                           const TypedefMap& type_params) {
  if (cls == nullptr || type.kind != DataTypeKind::kNamed ||
      type.packed_dim_left != nullptr || !type.extra_packed_dims.empty())
    return type;
  if (type.scope_name.empty() && !TypeParamNamedBy(cls, type.type_name).empty())
    return type;
  DataType cur = type;
  bool moved = false;
  for (int depth = 0; depth < 16 && cur.kind == DataTypeKind::kNamed; ++depth) {
    std::optional<DataType> next = NextAlong(cur, cls, type_params);
    if (!next.has_value()) break;
    cur = *next;
    moved = true;
  }
  bool aggregate = cur.kind == DataTypeKind::kStruct ||
                   cur.kind == DataTypeKind::kUnion ||
                   cur.kind == DataTypeKind::kEnum;
  return moved && !aggregate ? cur : type;
}

}  // namespace delta
