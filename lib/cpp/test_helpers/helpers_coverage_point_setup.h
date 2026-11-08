#pragma once

#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

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
