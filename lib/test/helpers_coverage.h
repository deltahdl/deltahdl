#pragma once

#include "simulation/coverage.h"

using namespace delta;

// Create a CoverGroup with two coverpoints ("a", "b") and a 2-bin cross.
inline CoverGroup* SetupTwoPointCross(CoverageDB& db) {
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "a");
  CoverageDB::AddCoverPoint(g, "b");
  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  CrossBin cb;
  cb.name = "a0_b0";
  cb.value_sets = {{0}, {0}};
  cross.bins.push_back(cb);
  cb.name = "a1_b1";
  cb.value_sets = {{1}, {1}};
  cross.bins.push_back(cb);
  CoverageDB::AddCross(g, cross);
  return g;
}
