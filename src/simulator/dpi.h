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

struct DpiArg {
  std::string_view name;
  DataTypeKind type = DataTypeKind::kInt;
  Direction direction = Direction::kInput;
  // Default value expression for the formal, if the import declared one. Used
  // when the call site omits this argument (see §35.6).
  const Expr* default_value = nullptr;
};

struct DpiFunction {
  std::string_view c_name;
  std::string_view sv_name;
  DataTypeKind return_type = DataTypeKind::kVoid;
  std::vector<DpiArg> args;
  std::function<uint64_t(const std::vector<uint64_t>&)> impl;
};

struct DpiImport {
  std::string_view c_name;
  std::string_view sv_name;
  bool is_pure = false;
};

struct DpiExport {
  std::string_view c_name;
  std::string_view sv_name;
};

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

// §H.13 bridge between the DPI C layer and the simulator's time state. The DPI
// time routines svGetTime/svGetTimeUnit/svGetTimePrecision (svdpi.cpp) report
// the same simulation time the VPI time routines do, but svdpi.cpp cannot pull
// in the VPI headers (their time constants and s_vpi_time spelling collide with
// svdpi.h's own). These accessors expose the design-wide time state as plain
// integers so the DPI layer stays free of those headers; the implementation
// lives in vpi.cpp where the VPI context is in scope.
//
// Report the current simulation time for the design as a whole (the time a NULL
// svScope selects). When want_scaled_real is true the time scaled to the
// simulation time unit is written to *real; otherwise the 64-bit
// simulation-time count is split into *high/*low. Equivalent to vpi_get_time()
// with a null object.
void DpiGetSimTime(bool want_scaled_real, uint32_t* high, uint32_t* low,
                   double* real);
// The design-wide simulation time unit and precision, equivalent to the values
// vpi_get() yields for vpiTimeUnit and vpiTimePrecision with a null object.
int32_t DpiGetSimTimeUnit();
int32_t DpiGetSimTimePrecision();

}  // namespace delta
