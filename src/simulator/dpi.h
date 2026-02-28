#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

// =============================================================================
// DPI argument descriptor
// =============================================================================

struct DpiArg {
  std::string_view name;
  DataTypeKind type = DataTypeKind::kInt;
  Direction direction = Direction::kInput;
};

// =============================================================================
// DpiFunction: a registered DPI-C function (import or export)
// =============================================================================

struct DpiFunction {
  std::string_view c_name;
  std::string_view sv_name;
  DataTypeKind return_type = DataTypeKind::kVoid;
  std::vector<DpiArg> args;
  std::function<uint64_t(const std::vector<uint64_t>&)> impl;
};

// =============================================================================
// DpiImport/DpiExport: declaration wrappers
// =============================================================================

struct DpiImport {
  std::string_view c_name;
  std::string_view sv_name;
  bool is_pure = false;
};

struct DpiExport {
  std::string_view c_name;
  std::string_view sv_name;
};

// =============================================================================
// DpiContext: manages registered DPI-C functions
// =============================================================================

class DpiContext {
 public:
  void RegisterImport(DpiFunction func);
  void RegisterExport(DpiExport exp);
  const DpiFunction* FindImport(std::string_view sv_name) const;
  uint64_t Call(std::string_view sv_name,
                const std::vector<uint64_t>& args) const;
  uint32_t ImportCount() const {
    return static_cast<uint32_t>(imports_.size());
  }
  uint32_t ExportCount() const {
    return static_cast<uint32_t>(exports_.size());
  }
  bool HasImport(std::string_view sv_name) const;
  bool HasExport(std::string_view sv_name) const;

 private:
  std::vector<DpiFunction> imports_;
  std::vector<DpiExport> exports_;
  std::unordered_map<std::string_view, size_t> import_index_;
  std::unordered_map<std::string_view, size_t> export_index_;
};

}  // namespace delta
