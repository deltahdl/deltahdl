#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;
struct ModuleItem;

struct DpiDimension {
  bool is_unsized = false;
  std::optional<int64_t> left;
  std::optional<int64_t> right;
  bool operator==(const DpiDimension&) const = default;
};

struct DpiTypeShape {
  DataTypeKind kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  std::string_view unresolved_name;
  bool has_unsized_packed_dim = false;
  std::vector<DpiDimension> packed_dims;
  std::vector<DpiDimension> unpacked_dims;
  bool operator==(const DpiTypeShape&) const = default;
};

struct DpiSignatureKey {
  DpiTypeShape return_type;
  bool is_pure = false;
  bool is_context = false;
  bool is_task = false;
  std::string_view spec_string;
  std::vector<std::pair<Direction, DpiTypeShape>> args;
};

struct DpiExportSignature {
  DpiTypeShape return_type;
  bool is_task = false;
  std::vector<std::pair<Direction, DpiTypeShape>> args;
  bool operator==(const DpiExportSignature&) const = default;
};

std::string_view DpiLinkageName(const ModuleItem* item);

DpiTypeShape BuildDpiTypeShape(const DataType& type,
                               const std::vector<Expr*>& unpacked_dims,
                               const TypedefMap& typedefs);

DpiSignatureKey BuildDpiSignature(const ModuleItem* item,
                                  const TypedefMap& typedefs);

bool DpiSignaturesMatch(const DpiSignatureKey& a, const DpiSignatureKey& b);

DpiExportSignature BuildDpiExportSignature(const ModuleItem* callable,
                                           const TypedefMap& typedefs);

}  // namespace delta
