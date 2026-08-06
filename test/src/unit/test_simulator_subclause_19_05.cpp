#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, AddCoverPointToGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  ASSERT_NE(cp, nullptr);
  EXPECT_EQ(cp->name, "addr");
  EXPECT_EQ(g->coverpoints.size(), 1u);
}

TEST(Coverage, IffGuardBlocksSampling) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = false;

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, IffGuardAllowsSampling) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = true;

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

// LRM 19.5: a value bin's count is incremented each time the coverage point
// matches one of the values in the bin's set.
TEST(Coverage, ValueBinCountIncrementsOnEachMatch) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin b;
  b.name = "set";
  b.values = {0, 1, 2};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 1}});
  db.Sample(g, {{"x", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 2u);
}

// LRM 19.5: a value outside the bin's set leaves its count unchanged.
TEST(Coverage, ValueBinCountUnchangedOnMiss) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin b;
  b.name = "set";
  b.values = {0, 1, 2};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 9}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

// LRM 19.5: a transition bin's count is incremented when the coverage point
// matches the entire sequence of value transitions.
TEST(Coverage, TransitionBinCountsOnSequenceMatch) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin t;
  t.name = "t01";
  t.kind = CoverBinKind::kTransition;
  t.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, t);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

// LRM 19.5: a transition bin does not count until the full sequence occurs.
TEST(Coverage, TransitionBinDoesNotCountWithoutSequence) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin t;
  t.name = "t01";
  t.kind = CoverBinKind::kTransition;
  t.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, t);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

// LRM 19.5: a transition bin counts only once the coverage point matches its
// entire sequence of value transitions, including a sequence of more than two
// states. The count advances on the sample that completes the full run.
TEST(Coverage, TransitionBinCountsOnMultiStepSequence) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin t;
  t.name = "t012";
  t.kind = CoverBinKind::kTransition;
  t.transitions = {{0, 1, 2}};
  CoverageDB::AddBin(cp, t);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
  db.Sample(g, {{"x", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

// LRM 19.5: a default bin catches values that do not lie within any of the
// defined bins.
TEST(Coverage, DefaultBinCatchesUnmatchedValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin defined;
  defined.name = "lo";
  defined.values = {0, 1};
  CoverageDB::AddBin(cp, defined);

  CoverBin def;
  def.name = "others";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  db.Sample(g, {{"x", 7}});
  EXPECT_EQ(g->coverpoints[0].bins[1].hit_count, 1u);
}

// LRM 19.5: the default bin shall not catch a value that already lies within a
// defined bin.
TEST(Coverage, DefaultBinSkipsDefinedValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin defined;
  defined.name = "lo";
  defined.values = {0, 1};
  CoverageDB::AddBin(cp, defined);

  CoverBin def;
  def.name = "others";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[1].hit_count, 0u);
}

// LRM 19.5: the number of automatically created bins is controlled by the
// auto_bin_max coverage option.
TEST(Coverage, AutoBinMaxControlsAutoBinCount) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 4;
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_EQ(cp->bins.size(), 4u);
}

// LRM 19.5: automatically created bins are distinguished from explicit bins.
TEST(Coverage, AutoBinsAreMarkedAuto) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 4;
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_EQ(cp->bins[0].kind, CoverBinKind::kAuto);
}

// LRM 19.5: automatic bins shall not be created for a coverpoint over a real
// expression; such a coverpoint must instead specify at least one explicit bins
// construct. Asking the engine to auto-create bins for a real coverpoint yields
// none, complementing the integral auto_bin_max case above.
TEST(Coverage, NoAutoBinsForRealCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 8;
  auto* cp = CoverageDB::AddCoverPoint(g, "r");
  cp->is_real = true;

  EXPECT_FALSE(CoverageDB::AutoBinsAllowed(cp));
  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_TRUE(cp->bins.empty());
}

// LRM 19.5: coverage calculation shall not take into account the coverage
// captured by default bins.
TEST(Coverage, DefaultBinExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin defined;
  defined.name = "lo";
  defined.values = {0};
  CoverageDB::AddBin(cp, defined);

  CoverBin def;
  def.name = "others";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  // Hit only the defined bin; the default bin remains unhit but must not drag
  // the coverpoint below 100%.
  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&g->coverpoints[0]), 100.0);
}

}  // namespace
