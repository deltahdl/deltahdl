#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"

namespace delta {

struct ClassDecl;
struct ClassMember;
struct DataType;
struct ModuleDecl;
struct ModuleItem;

enum class Constness : uint8_t {
  kWritable,
  kConstant,
  kConstantHandle,
  kEnumMember
};

enum class EnumMemberTargets : uint8_t { kSkipped, kCounted };

struct DeclaredName {
  Constness constness = Constness::kWritable;
  const ModuleDecl* instance_of = nullptr;
  size_t unpacked_dims = 0;
  const DataType* type = nullptr;
};

Constness ConstnessOfVariable(bool is_const, const DataType& type,
                              const NameSet& class_names);

std::optional<Constness> ConstnessOfItem(const ModuleItem* item,
                                         const NameSet& class_names);

bool CountsAsConstant(Constness constness, EnumMemberTargets enum_members);

void ForEachDeclaredEnumMember(const DataType& type,
                               const std::function<void(std::string_view)>& fn);

const DataType& DeclaredTypeOf(const ModuleItem* item);

const DataType& MemberDeclaredType(const ClassMember* m);

std::optional<DeclaredName> DeclaredAmong(const std::vector<ModuleItem*>& items,
                                          std::string_view name,
                                          const NameSet& class_names);

std::optional<Constness> ConstnessAmong(const std::vector<ModuleItem*>& items,
                                        std::string_view name,
                                        const NameSet& class_names);

std::optional<Constness> ConstnessInModule(const ModuleDecl* decl,
                                           std::string_view name,
                                           const NameSet& class_names);

std::optional<Constness> ConstnessInClass(const ClassDecl* cls,
                                          std::string_view name);

}  // namespace delta
