#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_coverage.h"
#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, CrossCoverageCreation) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);
  EXPECT_EQ(g->crosses.size(), 1u);
  EXPECT_EQ(g->crosses[0].bins.size(), 2u);
}

TEST(Coverage, CrossCoverageSampling) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);

  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(g->crosses[0].bins[0].hit_count, 1u);
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 0u);

  db.Sample(g, {{"a", 1}, {"b", 1}});
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 1u);
}

// Helper: a coverpoint with explicitly-named integral bins.
static CoverPoint* AddPointWithBins(CoverGroup* g, const std::string& name,
                                    const std::vector<int64_t>& bin_values) {
  auto* cp = CoverageDB::AddCoverPoint(g, name);
  for (int64_t v : bin_values) {
    CoverBin b;
    b.name = "b" + std::to_string(v);
    b.values = {v};
    CoverageDB::AddBin(cp, b);
  }
  return cp;
}

// LRM 19.6: cross coverage of N coverage points is the Cartesian product of
// their bins.
TEST(Coverage, CrossCartesianProduct) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0, 1});
  AddPointWithBins(g, "b", {0, 1, 2});

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));

  CoverageDB::AutoCreateCrossBins(g, xc);
  EXPECT_EQ(xc->bins.size(), 6u);  // 2 * 3

  // Sampling a matching combination hits exactly one cross product bin.
  db.Sample(g, {{"a", 1}, {"b", 2}});
  uint64_t total_hits = 0;
  for (const auto& cb : xc->bins) total_hits += cb.hit_count;
  EXPECT_EQ(total_hits, 1u);
}

// LRM 19.6: no cross product bins are created for coverpoint bins that are
// default, ignore, or illegal bins.
TEST(Coverage, CrossExcludesDefaultIgnoreIllegalBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* a = AddPointWithBins(g, "a", {0});  // one explicit bin
  CoverBin def;
  def.name = "rest";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(a, def);
  CoverBin ign;
  ign.name = "skip";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {9};
  CoverageDB::AddBin(a, ign);

  AddPointWithBins(g, "b", {0, 1});  // two explicit bins

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));

  CoverageDB::AutoCreateCrossBins(g, xc);
  // Only the one explicit bin of "a" contributes: 1 * 2 == 2.
  EXPECT_EQ(xc->bins.size(), 2u);
}

// LRM 19.6: a bare variable used in a cross is given an implicit coverpoint.
TEST(Coverage, CrossCreatesImplicitCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0, 1});  // "a" already a coverpoint

  CoverageDB::EnsureCrossCoverPoints(g, {"a", "v"});
  EXPECT_EQ(g->coverpoints.size(), 2u);  // "v" created implicitly
  EXPECT_EQ(g->coverpoints.back().name, "v");
}

// LRM 19.6: cross items must resolve to coverpoints of the same covergroup.
TEST(Coverage, CrossItemsMustBeInSameGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0});
  AddPointWithBins(g, "b", {0});

  EXPECT_TRUE(CoverageDB::CrossItemsInSameGroup(g, {"a", "b"}));
  EXPECT_FALSE(CoverageDB::CrossItemsInSameGroup(g, {"a", "elsewhere"}));
}

// LRM 19.6: a real variable cannot be crossed directly, but a coverpoint of a
// real expression can participate.
TEST(Coverage, CrossRejectsBareRealVariable) {
  EXPECT_TRUE(CoverageDB::CrossBareVariableAllowed(/*variable_is_real=*/false));
  EXPECT_FALSE(CoverageDB::CrossBareVariableAllowed(/*variable_is_real=*/true));

  // A coverpoint of a real expression is a coverpoint and may be crossed.
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* rp = CoverageDB::AddCoverPoint(g, "rexpr");
  rp->is_real = true;
  EXPECT_TRUE(CoverageDB::CrossItemsInSameGroup(g, {"rexpr"}));
}

// LRM 19.6: a false cross-level iff guard ignores the whole cross; a false
// per-bin iff guard ignores just that bin.
TEST(Coverage, CrossIffGuards) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);
  auto& cross = g->crosses[0];

  cross.has_iff_guard = true;
  cross.iff_guard_value = false;
  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(cross.bins[0].hit_count, 0u);  // whole cross ignored

  cross.iff_guard_value = true;
  cross.bins[0].has_iff_guard = true;
  cross.bins[0].iff_guard_value = false;
  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(cross.bins[0].hit_count, 0u);  // this bin ignored

  cross.bins[0].iff_guard_value = true;
  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(cross.bins[0].hit_count, 1u);  // now counted
}

// LRM 19.6: the cross label provides the cross's name and is the scope that
// owns the bins defined within the cross.
TEST(Coverage, CrossLabelNamesAndScopesBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0, 1});
  AddPointWithBins(g, "b", {0, 1});

  CrossCover cross;
  cross.name = "aXb";  // the label
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));
  CoverageDB::AutoCreateCrossBins(g, xc);

  // The label names the cross, and its bins are reached only through it.
  EXPECT_EQ(xc->name, "aXb");
  EXPECT_EQ(g->crosses.size(), 1u);
  EXPECT_EQ(g->crosses[0].name, "aXb");
  EXPECT_FALSE(g->crosses[0].bins.empty());
}

// LRM 19.6 (edge case): cross coverage generalizes to more than two coverage
// points -- the product is taken across all of them.
TEST(Coverage, CrossCartesianProductThreeWay) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0, 1});
  AddPointWithBins(g, "b", {0, 1, 2});
  AddPointWithBins(g, "c", {0, 1});

  CrossCover cross;
  cross.name = "aXbXc";
  cross.coverpoint_names = {"a", "b", "c"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));
  CoverageDB::AutoCreateCrossBins(g, xc);
  EXPECT_EQ(xc->bins.size(), 12u);  // 2 * 3 * 2
}

// LRM 19.6 (edge case): when a crossed coverpoint contributes no eligible bins
// -- here it has only an illegal bin -- the whole cross product is empty.
TEST(Coverage, CrossEmptyWhenCoverpointHasNoEligibleBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* a = CoverageDB::AddCoverPoint(g, "a");
  CoverBin bad;
  bad.name = "bad";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {0};
  CoverageDB::AddBin(a, bad);  // only an illegal bin contributes nothing
  AddPointWithBins(g, "b", {0, 1});

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));
  CoverageDB::AutoCreateCrossBins(g, xc);
  EXPECT_TRUE(xc->bins.empty());
}

}  // namespace
