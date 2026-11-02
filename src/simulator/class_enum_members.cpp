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

// The enumeration `member` declares, inline on a property, `enum {a, b} e;`,
// or by a typedef of the class, with the key it is registered under; null
// for any other member.
static const DataType* DeclaredEnumOf(const ClassTypeInfo* info,
                                      const ClassMember* member,
                                      std::string& key) {
  const DataType* type = nullptr;
  if (member->kind == ClassMemberKind::kProperty &&
      member->data_type.kind == DataTypeKind::kEnum) {
    // §6.19 with §8.5: under the property's own key (ClassInlineEnumKey),
    // which EnumTypeOfClassMember resolves the property's type by.
    type = &member->data_type;
    key = ClassInlineEnumKey(info->name, member->name);
  } else if (member->kind == ClassMemberKind::kTypedef &&
             member->typedef_item != nullptr) {
    type = &member->typedef_item->typedef_type;
    key = std::string(info->name) + "::" + std::string(member->name);
  }
  return type != nullptr && !type->enum_members.empty() ? type : nullptr;
}

// §8.23 with §6.19: the literals of every enumeration a typedef of the class
// declares, or a property of it declares inline, each bound in the class
// scope, and the enumeration itself registered under "Class::name" or the
// property's key (DeclaredEnumOf), the key a property or a variable declared
// with it resolves its type by (EnumTypeOfDeclaredType in eval_enum.cpp), so
// that §6.19.5's methods on such a value have members to walk. A nested class's
// typedef is entered by no other path: the design's typedef table
// (RtlirDesign::type_enums) holds the unit's classes alone.
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
    // §6.19: the values fold as the module's constants do, a negative value
    // and the range forms included, and a literal reads at the enumeration's
    // width and signing (ClassEnumLiteral).
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
