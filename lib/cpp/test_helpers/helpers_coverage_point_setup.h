#pragma once

#include "simulator/coverage.h"

using namespace delta;

// Add a coverpoint "x" to |g| with two user-defined value bins, b0 matching
// value 0 and b1 matching value 1, and return the new coverpoint.
inline CoverPoint* AddTwoValueBinPoint(CoverGroup* g) {
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);
  CoverBin b1;
  b1.name = "b1";
  b1.values = {1};
  CoverageDB::AddBin(cp, b1);
  return cp;
}
