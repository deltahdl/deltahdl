#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;

struct DeclaredValue {
  DataType type;
  uint32_t unpacked_dims = 0;
  UnpackedKind outermost = UnpackedKind::kFixed;
  std::optional<DataType> index_type = {};
  std::vector<Expr*> dims = {};
};

struct ExprTypeScope {
  std::function<std::optional<DeclaredValue>(std::string_view)> value_named;
  std::function<std::optional<DataType>(const Expr*)> call_returns;
  std::function<std::optional<DataType>(const Expr*)> type_ref;
  const TypedefMap& typedefs;
  const ScopeMap& constants;
  Arena& arena;
  std::string_view iterator = {};
  std::optional<DataType> iterator_index = {};
  const TypeShapeTables* array_tables = nullptr;
  std::function<std::optional<UnpackedArrayType>(const DataType&,
                                                 std::string_view)>
      class_member = {};
  std::function<std::optional<DeclaredValue>(std::string_view prefix,
                                             std::string_view name)>
      scoped_value = {};
};

DataType VectorType(uint32_t width, bool is_signed, bool four_state,
                    Arena& arena);

std::optional<DataType> ExprSelfType(const Expr* expr,
                                     const ExprTypeScope& scope);

std::optional<UnpackedArrayType> ExprSelfArrayType(const Expr* expr,
                                                   const ExprTypeScope& scope);

DeclaredValue UnderDims(DataType type, const std::vector<Expr*>& dims,
                        const ExprTypeScope& scope);

std::optional<DeclaredValue> ExprValue(const Expr* expr,
                                       const ExprTypeScope& scope);

std::optional<UnpackedArrayType> ValueArrayType(const DeclaredValue& value);

}  // namespace delta
