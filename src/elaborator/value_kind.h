#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "elaborator/elaborator_data.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;
struct ModuleItem;

enum class ValueKind : uint8_t { kUnknown, kIntegral, kReal, kString, kOther };

struct ValueIterator {
  std::string_view name;
  const ElaboratorData::VarArrayInfo* array = nullptr;
};

struct ValueScope {
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  const std::unordered_map<std::string_view, std::string_view>& var_named_types;
  const std::unordered_map<std::string_view, ElaboratorData::VarArrayInfo>&
      arrays;
  const std::unordered_map<std::string_view, const ModuleItem*>& functions;
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
  ValueIterator iterator = {};
};

ValueKind KindOfTypeKind(DataTypeKind kind);

ValueKind KindOfValue(const Expr* e, const ValueScope& scope);

ValueKind KindOfElement(const ElaboratorData::VarArrayInfo& info,
                        const ValueScope& scope);

const StructMember* SelectedStructMember(const Expr* e,
                                         const ValueScope& scope);

}  // namespace delta
