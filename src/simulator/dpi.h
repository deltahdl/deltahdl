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
  // §35.2.2.1: "The implementation (representation and layout) of 4-state
  // values ... is irrelevant for SystemVerilog semantics and can only impact
  // the foreign side of the interface." A value crosses as the aval/bval pair
  // Logic4Word holds, because a 4-state bit needs two bits to say it is x or z
  // and a bare word has one. Carried as a word instead, a design's x came back
  // 0 and no import could return one.
  std::function<Logic4Word(const std::vector<Logic4Word>&)> impl;
  // The same foreign function, reached where it writes its arguments as well as
  // reading them. §35.5.1.2 has the changes an imported function makes to an
  // output or an inout formal be visible outside the call, and `impl` is handed
  // its arguments by const reference, so a function declared with either
  // direction needs this form to say anything through them. A function with
  // input formals alone is complete as `impl`, which is what most imports are
  // and what every import written before the directions were carried is.
  std::function<Logic4Word(std::vector<Logic4Word>&)> arg_impl;
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
  Logic4Word Call(std::string_view sv_name,
                  const std::vector<Logic4Word>& args) const;
  // Calls the import with arguments it may write, and leaves in `args` what the
  // foreign function left there. Which of those values reaches the call site is
  // §35.5.1.2's question rather than this one's: the answer is applied by the
  // caller, which knows the actual each formal was written against.
  Logic4Word CallWithArgs(std::string_view sv_name,
                          std::vector<Logic4Word>& args) const;
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
