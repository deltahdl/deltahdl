#include "simulator/dpi_side.h"

#include <string_view>

#include "simulator/dpi_runtime.h"

namespace delta {

std::string_view DpiSideDescribedIn(DpiSide side) {
  // §H.1: the annex is the foreign language side's; Clause 35 is the
  // SystemVerilog side's.
  return side == DpiSide::kForeign ? "H" : "35";
}

DpiSide DpiImplementingSide(const DpiRtFunction& /*import*/) {
  // §H.2: functions implemented in C and given import declarations.
  return DpiSide::kForeign;
}

DpiSide DpiCallingSide(const DpiRtFunction& /*import*/) {
  // §H.2: ... can be called from SystemVerilog.
  return DpiSide::kSystemVerilog;
}

DpiSide DpiImplementingSide(const DpiRtExport& /*exported*/) {
  // §H.2: functions and tasks implemented in SystemVerilog and specified in
  // export declarations.
  return DpiSide::kSystemVerilog;
}

DpiSide DpiCallingSide(const DpiRtExport& /*exported*/) {
  // §H.2: ... can be called from C.
  return DpiSide::kForeign;
}

std::string_view DpiNameOnSide(const DpiRtFunction& import, DpiSide side) {
  // §35.4: the foreign side's name is the global linkage name, which is the
  // SystemVerilog name where the declaration gives none.
  return side == DpiSide::kForeign ? DpiGlobalName(import) : import.sv_name;
}

std::string_view DpiNameOnSide(const DpiRtExport& exported, DpiSide side) {
  return side == DpiSide::kForeign ? DpiGlobalName(exported) : exported.sv_name;
}

}  // namespace delta
