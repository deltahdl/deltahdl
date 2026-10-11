#pragma once

// §10.3.4 and §28.11: the drive strengths of a continuous assignment as the
// lowerer reads them. Split out of simulator/lowerer_contassign.cpp, which
// lowers the assignment and runs its process, because that file reached the
// line limit assert-no-oversized-source-files holds sources to.

#include <cstdint>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

class Arena;

// The strength a parser strength code names: 1 to 5 for highz, weak, pull,
// strong and supply, and strong for any other code, which is what an
// assignment writing no strength carries (§10.3.4's default).
Strength StrengthFromParserCode(uint8_t s);

// §28.11: the value `val` drives with the strengths `ds`, every bit a highz
// strength covers being z. Defined in simulator/contassign_strength.cpp.
Logic4Vec ApplyHighzStrengthsToValue(const Logic4Vec& val, DriverStrength ds,
                                     Arena& arena);

}  // namespace delta
