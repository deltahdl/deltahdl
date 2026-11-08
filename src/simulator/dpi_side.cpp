#include "simulator/dpi_side.h"

#include <string_view>

#include "simulator/dpi_runtime.h"

namespace delta {

std::string_view DpiSideDescribedIn(DpiSide side) {
  return side == DpiSide::kForeign ? "H" : "35";
}

DpiSide DpiImplementingSide(const DpiRtFunction&) { return DpiSide::kForeign; }

DpiSide DpiCallingSide(const DpiRtFunction&) { return DpiSide::kSystemVerilog; }

DpiSide DpiImplementingSide(const DpiRtExport&) {
  return DpiSide::kSystemVerilog;
}

DpiSide DpiCallingSide(const DpiRtExport&) { return DpiSide::kForeign; }

DpiSubroutineKind DpiKindOf(const DpiRtFunction& import) {
  return import.is_task ? DpiSubroutineKind::kImportedTask
                        : DpiSubroutineKind::kImportedFunction;
}

DpiSubroutineKind DpiKindOf(const DpiRtExport& exported) {
  return exported.is_task ? DpiSubroutineKind::kExportedTask
                          : DpiSubroutineKind::kExportedFunction;
}

bool DpiKindMayCallExportedTask(DpiSubroutineKind kind) {
  switch (kind) {
    case DpiSubroutineKind::kImportedTask:
    case DpiSubroutineKind::kExportedTask:
      return true;
    case DpiSubroutineKind::kImportedFunction:
    case DpiSubroutineKind::kExportedFunction:
      return false;
  }
  return false;
}

std::string_view DpiNameOnSide(const DpiRtFunction& import, DpiSide side) {
  return side == DpiSide::kForeign ? DpiGlobalName(import) : import.sv_name;
}

std::string_view DpiNameOnSide(const DpiRtExport& exported, DpiSide side) {
  return side == DpiSide::kForeign ? DpiGlobalName(exported) : exported.sv_name;
}

}  // namespace delta
