#pragma once

#include <cstdint>
#include <string_view>

#include "simulator/dpi_runtime.h"

namespace delta {

// §H.1: Annex H describes the foreign language side of the direct programming
// interface. The DPI has two sides, the SystemVerilog side that Clause 35
// describes and the foreign language side, a C function call protocol and
// linking model, that the annex describes; a subroutine crossing the
// interface is implemented on one side and called from the other, and is
// known on each side by that side's name for it -- the SystemVerilog name of
// its declaration on the SystemVerilog side, and its global linkage name on
// the foreign side. This file names the two sides so that the runtime's
// records of imports and exports can be read side by side.
enum class DpiSide : std::uint8_t { kSystemVerilog, kForeign };

// §H.1: the clause of the standard describing a side -- Annex H for the
// foreign language side, Clause 35 for the SystemVerilog side.
std::string_view DpiSideDescribedIn(DpiSide side);

// §H.2 under §H.1: an imported subroutine is implemented on the foreign side
// and called from the SystemVerilog side; an exported one is implemented on
// the SystemVerilog side and called from the foreign side.
DpiSide DpiImplementingSide(const DpiRtFunction& import);
DpiSide DpiCallingSide(const DpiRtFunction& import);
DpiSide DpiImplementingSide(const DpiRtExport& exported);
DpiSide DpiCallingSide(const DpiRtExport& exported);

// §H.1 with §35.4: the name a subroutine is known by on a side -- the
// SystemVerilog name on the SystemVerilog side, the global linkage name on
// the foreign side, which is the SystemVerilog name where the declaration
// gives no other.
std::string_view DpiNameOnSide(const DpiRtFunction& import, DpiSide side);
std::string_view DpiNameOnSide(const DpiRtExport& exported, DpiSide side);

}  // namespace delta
