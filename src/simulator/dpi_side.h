#pragma once

#include <cstdint>
#include <string_view>

#include "simulator/dpi_runtime.h"

namespace delta {

enum class DpiSide : std::uint8_t { kSystemVerilog, kForeign };

std::string_view DpiSideDescribedIn(DpiSide side);

DpiSide DpiImplementingSide(const DpiRtFunction& import);
DpiSide DpiCallingSide(const DpiRtFunction& import);
DpiSide DpiImplementingSide(const DpiRtExport& exported);
DpiSide DpiCallingSide(const DpiRtExport& exported);

enum class DpiSubroutineKind : std::uint8_t {
  kImportedFunction,
  kExportedFunction,
  kExportedTask,
  kImportedTask,
};
DpiSubroutineKind DpiKindOf(const DpiRtFunction& import);
DpiSubroutineKind DpiKindOf(const DpiRtExport& exported);

bool DpiKindMayCallExportedTask(DpiSubroutineKind kind);

std::string_view DpiNameOnSide(const DpiRtFunction& import, DpiSide side);
std::string_view DpiNameOnSide(const DpiRtExport& exported, DpiSide side);

}  // namespace delta
