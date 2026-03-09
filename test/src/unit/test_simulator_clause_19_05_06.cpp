#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, IllegalBinsNotSampled) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin ib;
  ib.name = "bad_addr";
  ib.kind = CoverBinKind::kIllegal;
  ib.values = {0xFF};
  CoverageDB::AddBin(cp, ib);

  db.Sample(g, {{"addr", 0xFF}});

  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, IllegalBinsExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin good;
  good.name = "valid";
  good.values = {1};
  CoverageDB::AddBin(cp, good);

  CoverBin bad;
  bad.name = "illegal";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {0xFF};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"x", 1}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

}
