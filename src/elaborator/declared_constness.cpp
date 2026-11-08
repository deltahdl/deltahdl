#include "elaborator/declared_constness.h"

#include <functional>
#include <optional>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

bool IsHandleType(const DataType& type, const NameSet& class_names) {
  return type.kind == DataTypeKind::kVirtualInterface ||
         (type.kind == DataTypeKind::kNamed &&
          class_names.count(type.type_name) != 0);
}

bool DeclaresEnumMember(const DataType& type, std::string_view name) {
  bool declares = false;
  ForEachDeclaredEnumMember(type, [name, &declares](std::string_view member) {
    declares = declares || member == name;
  });
  return declares;
}

}  // namespace

Constness ConstnessOfVariable(bool is_const, const DataType& type,
                              const NameSet& class_names) {
  if (!is_const) return Constness::kWritable;
  return IsHandleType(type, class_names) ? Constness::kConstantHandle
                                         : Constness::kConstant;
}

std::optional<Constness> ConstnessOfItem(const ModuleItem* item,
                                         const NameSet& class_names) {
  switch (item->kind) {
    case ModuleItemKind::kParamDecl:
    case ModuleItemKind::kSpecparam:
      return Constness::kConstant;
    case ModuleItemKind::kVarDecl:
      return ConstnessOfVariable(item->data_type.is_const, item->data_type,
                                 class_names);
    case ModuleItemKind::kNetDecl:
      return Constness::kWritable;
    default:
      return std::nullopt;
  }
}

bool CountsAsConstant(Constness constness, EnumMemberTargets enum_members) {
  if (constness == Constness::kEnumMember)
    return enum_members == EnumMemberTargets::kCounted;
  return constness != Constness::kWritable;
}

void ForEachDeclaredEnumMember(
    const DataType& type, const std::function<void(std::string_view)>& fn) {
  ForEachEnumTypeIn(type, [&fn](std::string_view, const DataType& enum_type) {
    for (const EnumMember& member : enum_type.enum_members) {
      if (member.range_start == nullptr) fn(member.name);
    }
  });
}

const DataType& DeclaredTypeOf(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kTypedef ? item->typedef_type
                                                : item->data_type;
}

const DataType& MemberDeclaredType(const ClassMember* m) {
  return m->typedef_item != nullptr ? DeclaredTypeOf(m->typedef_item)
                                    : m->data_type;
}

std::optional<DeclaredName> DeclaredAmong(const std::vector<ModuleItem*>& items,
                                          std::string_view name,
                                          const NameSet& class_names) {
  for (const ModuleItem* item : items) {
    std::optional<Constness> constness =
        item->name == name ? ConstnessOfItem(item, class_names) : std::nullopt;
    if (constness.has_value())
      return DeclaredName{*constness, nullptr, item->unpacked_dims.size(),
                          &item->data_type};
    if (DeclaresEnumMember(DeclaredTypeOf(item), name))
      return DeclaredName{Constness::kEnumMember, nullptr, 0, nullptr};
  }
  return std::nullopt;
}

std::optional<Constness> ConstnessAmong(const std::vector<ModuleItem*>& items,
                                        std::string_view name,
                                        const NameSet& class_names) {
  std::optional<DeclaredName> declared =
      DeclaredAmong(items, name, class_names);
  if (!declared.has_value()) return std::nullopt;
  return declared->constness;
}

std::optional<Constness> ConstnessInModule(const ModuleDecl* decl,
                                           std::string_view name,
                                           const NameSet& class_names) {
  for (const auto& [param, value] : decl->params) {
    if (param == name) return Constness::kConstant;
  }
  if (DeclaredSpecparamNames(decl).contains(name)) return Constness::kConstant;
  return ConstnessAmong(decl->items, name, class_names);
}

std::optional<Constness> ConstnessInClass(const ClassDecl* cls,
                                          std::string_view name) {
  for (const auto& [param, value] : cls->params) {
    if (param == name) return Constness::kConstant;
  }
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->name == name)
      return m->is_param ? Constness::kConstant : Constness::kWritable;
    if (DeclaresEnumMember(MemberDeclaredType(m), name))
      return Constness::kEnumMember;
  }
  return std::nullopt;
}

}  // namespace delta
