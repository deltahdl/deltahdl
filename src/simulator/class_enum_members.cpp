#include "simulator/class_enum_members.h"

#include <string>
#include <utility>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

static const DataType* DeclaredEnumOf(const ClassTypeInfo* info,
                                      const ClassMember* member,
                                      std::string& key) {
  const DataType* type = nullptr;
  if (member->kind == ClassMemberKind::kProperty &&
      member->data_type.kind == DataTypeKind::kEnum) {
    type = &member->data_type;
    key = ClassInlineEnumKey(info->name, member->name);
  } else if (member->kind == ClassMemberKind::kTypedef &&
             member->typedef_item != nullptr) {
    type = &member->typedef_item->typedef_type;
    key = std::string(info->name) + "::" + std::string(member->name);
  }
  return type != nullptr && !type->enum_members.empty() ? type : nullptr;
}

void CollectClassEnumMembers(ClassTypeInfo* info, const ClassDecl* cls,
                             SimContext& ctx, Arena& arena) {
  for (const auto* member : cls->members) {
    std::string key;
    const DataType* decl_type = DeclaredEnumOf(info, member, key);
    if (decl_type == nullptr) continue;
    EnumTypeInfo type;
    type.type_name = *arena.Create<std::string>(std::move(key));
    type.width = EvalTypeWidth(*decl_type);
    type.is_4state = Is4stateType(*decl_type, TypedefMap{});
    type.is_signed = IsSignedType(*decl_type, TypedefMap{});
    for (const RtlirEnumMember& m :
         FoldEnumMembers(decl_type->enum_members, ScopeMap{}, arena)) {
      EnumMemberInfo member = EnumMemberInfoOf(m, type.width, ctx, arena);
      info->enum_members[std::string(m.name)] = member.value;
      info->enum_literal_shapes[std::string(m.name)] = {type.width,
                                                        type.is_signed};
      type.members.push_back(member);
    }
    if (ctx.FindEnumType(type.type_name) == nullptr)
      ctx.RegisterEnumType(type.type_name, type);
  }
}

}  // namespace delta
