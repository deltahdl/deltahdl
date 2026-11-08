#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

enum class CheckerStatementKind : uint8_t {
  kChangeSensitive,
  kBlocking,
  kCheckerVariableNonblocking,
};

Region HomeRegionForCheckerStatement(CheckerStatementKind kind);

Region ConcurrentAssertionRegionInChecker(Region region_in_design_code);

}  // namespace delta
