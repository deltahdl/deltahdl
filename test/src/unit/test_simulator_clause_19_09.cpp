#include <gtest/gtest.h>

#include <fstream>
#include <string>
#include <vector>

#include "helpers_scheduler.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// LRM 19.9: $load_coverage_db loads cumulative coverage information for all
// coverage group types. Loaded hit counts accumulate onto the live database for
// a covergroup type that already exists.
TEST(Coverage, LoadCumulativeCoverageAccumulatesHits) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);
  CoverBin b1;
  b1.name = "b1";
  b1.values = {1};
  CoverageDB::AddBin(cp, b1);

  // Live run only ever sampled b0, so half the bins are covered.
  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 50.0);

  // A persisted run of the same covergroup type had covered b1.
  CoverGroup loaded;
  loaded.name = "cg";
  loaded.sample_count = 1;
  CoverPoint lcp;
  lcp.name = "x";
  CoverBin lb1;
  lb1.name = "b1";
  lb1.values = {1};
  lb1.hit_count = 1;
  lcp.bins.push_back(lb1);
  loaded.coverpoints.push_back(lcp);

  db.MergeCumulativeCoverage({loaded});

  // The two runs together cover both bins, and the sample counts add up.
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 100.0);
  EXPECT_EQ(db.FindGroup("cg")->sample_count, 2u);
}

// LRM 19.9: a covergroup type present only in the loaded cumulative coverage is
// added to the database.
TEST(Coverage, LoadCumulativeCoverageAddsAbsentType) {
  CoverageDB db;
  EXPECT_EQ(db.GroupCount(), 0u);

  CoverGroup loaded;
  loaded.name = "cg2";
  loaded.sample_count = 3;
  db.MergeCumulativeCoverage({loaded});

  EXPECT_EQ(db.GroupCount(), 1u);
  ASSERT_NE(db.FindGroup("cg2"), nullptr);
  EXPECT_EQ(db.FindGroup("cg2")->sample_count, 3u);
}

// LRM 19.9 edge case: loading an empty cumulative set leaves the database
// untouched.
TEST(Coverage, LoadCumulativeCoverageEmptyIsNoOp) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "x");
  g->sample_count = 5;

  db.MergeCumulativeCoverage({});

  EXPECT_EQ(db.GroupCount(), 1u);
  EXPECT_EQ(db.FindGroup("cg")->sample_count, 5u);
}

// LRM 19.9: a coverpoint present only in the loaded cumulative coverage is
// appended to the matching live covergroup type.
TEST(Coverage, LoadCumulativeCoverageAppendsNewCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "x");

  CoverGroup loaded;
  loaded.name = "cg";
  CoverPoint lcp;
  lcp.name = "y";
  CoverBin lb;
  lb.name = "yb0";
  lb.values = {0};
  lb.hit_count = 1;
  lcp.bins.push_back(lb);
  loaded.coverpoints.push_back(lcp);

  db.MergeCumulativeCoverage({loaded});

  auto* live = db.FindGroup("cg");
  ASSERT_EQ(live->coverpoints.size(), 2u);
  EXPECT_EQ(live->coverpoints[1].name, "y");
  EXPECT_EQ(live->coverpoints[1].bins.at(0).hit_count, 1u);
}

// LRM 19.9: a bin present only in the loaded cumulative coverage is appended to
// the matching live coverpoint rather than merged into an existing bin.
TEST(Coverage, LoadCumulativeCoverageAppendsNewBin) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);

  CoverGroup loaded;
  loaded.name = "cg";
  CoverPoint lcp;
  lcp.name = "x";
  CoverBin lb;
  lb.name = "bnew";
  lb.values = {7};
  lb.hit_count = 2;
  lcp.bins.push_back(lb);
  loaded.coverpoints.push_back(lcp);

  db.MergeCumulativeCoverage({loaded});

  auto& bins = db.FindGroup("cg")->coverpoints.at(0).bins;
  ASSERT_EQ(bins.size(), 2u);
  EXPECT_EQ(bins[0].name, "b0");
  EXPECT_EQ(bins[1].name, "bnew");
  EXPECT_EQ(bins[1].hit_count, 2u);
}

// LRM 19.9: cross coverage is also part of the cumulative coverage. Loaded
// cross-bin hit counts accumulate onto a matching live cross, and a cross seen
// only in the loaded data is appended.
TEST(Coverage, LoadCumulativeCoverageMergesCrosses) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CrossCover live_cross;
  live_cross.name = "xy";
  CrossBin live_bin;
  live_bin.name = "cb";
  live_bin.hit_count = 1;
  live_cross.bins.push_back(live_bin);
  CoverageDB::AddCross(g, live_cross);

  CoverGroup loaded;
  loaded.name = "cg";
  CrossCover loaded_match;
  loaded_match.name = "xy";
  CrossBin loaded_bin;
  loaded_bin.name = "cb";
  loaded_bin.hit_count = 4;
  loaded_match.bins.push_back(loaded_bin);
  loaded.crosses.push_back(loaded_match);
  CrossCover loaded_new;
  loaded_new.name = "zw";
  loaded.crosses.push_back(loaded_new);

  db.MergeCumulativeCoverage({loaded});

  auto& crosses = db.FindGroup("cg")->crosses;
  ASSERT_EQ(crosses.size(), 2u);
  EXPECT_EQ(crosses[0].name, "xy");
  EXPECT_EQ(crosses[0].bins.at(0).hit_count, 5u);
  EXPECT_EQ(crosses[1].name, "zw");
}

// LRM 19.9: $get_coverage() reports the overall coverage of *all* coverage
// group types, so its value aggregates across more than one covergroup type. A
// fully covered type and a half-covered type of equal weight average to 75.
TEST(Coverage, GetCoverageAggregatesAcrossTypes) {
  CoverageDB db;

  auto* a = db.CreateGroup("cg_a");
  auto* acp = CoverageDB::AddCoverPoint(a, "x");
  CoverBin ab0;
  ab0.name = "b0";
  ab0.values = {0};
  CoverageDB::AddBin(acp, ab0);
  CoverBin ab1;
  ab1.name = "b1";
  ab1.values = {1};
  CoverageDB::AddBin(acp, ab1);
  db.Sample(a, {{"x", 0}});
  db.Sample(a, {{"x", 1}});  // both bins hit -> cg_a is 100% covered

  auto* b = db.CreateGroup("cg_b");
  auto* bcp = CoverageDB::AddCoverPoint(b, "y");
  CoverBin bb0;
  bb0.name = "b0";
  bb0.values = {0};
  CoverageDB::AddBin(bcp, bb0);
  CoverBin bb1;
  bb1.name = "b1";
  bb1.values = {1};
  CoverageDB::AddBin(bcp, bb1);
  db.Sample(b, {{"y", 0}});  // only one of two bins hit -> cg_b is 50% covered

  // Overall coverage spans both types: (100 + 50) / 2 with equal weights.
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 75.0);
}

// LRM 19.9: $load_coverage_db loads cumulative coverage for all coverage group
// types, so a single load can touch more than one type at once.
TEST(Coverage, LoadCumulativeCoverageHandlesMultipleTypes) {
  CoverageDB db;
  auto* a = db.CreateGroup("cg_a");
  a->sample_count = 1;
  auto* b = db.CreateGroup("cg_b");
  b->sample_count = 2;

  CoverGroup la;
  la.name = "cg_a";
  la.sample_count = 10;
  CoverGroup lb;
  lb.name = "cg_b";
  lb.sample_count = 20;
  db.MergeCumulativeCoverage({la, lb});

  EXPECT_EQ(db.FindGroup("cg_a")->sample_count, 11u);
  EXPECT_EQ(db.FindGroup("cg_b")->sample_count, 22u);
}

// --- LRM 19.9: the predefined coverage system tasks/functions driven from real
// source through the full pipeline (parse, elaborate, lower, run). These
// observe the production dispatch that wires $get_coverage / $load_coverage_db
// / $set_coverage_db_name to the run's live coverage database.
// -----------------

// $get_coverage() is a system function returning the overall coverage of all
// coverage group types as a real in the range 0 to 100. A design with no
// coverage data reports 0.
TEST(Coverage, GetCoverageSyscallEmptyDesignReturnsRealZero) {
  const std::string src =
      "module t;\n"
      "  real cov;\n"
      "  initial cov = $get_coverage();\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(src, "cov"), 0.0);
}

// Writes a coverage snapshot in the format LoadCoverageDbFile parses: a single
// covergroup type "cg" with one coverpoint "x" whose two bins are `covered`.
static std::string WriteSnapshot(const std::string& tag, bool second_bin_hit) {
  std::string path = testing::TempDir() + "delta_cov_19_09_" + tag + ".txt";
  std::ofstream out(path);
  out << "CG cg 1\n"
      << "CP x\n"
      << "BIN b0 0 1\n"
      << "BIN b1 1 " << (second_bin_hit ? "2" : "0") << "\n";
  return path;
}

// $load_coverage_db(filename) loads the cumulative coverage of a prior run, and
// $get_coverage() then reflects it. Here the snapshot covered one of the two
// bins of covergroup type cg, so overall coverage is 50%.
TEST(Coverage, LoadCoverageDbSyscallThenGetCoverageHalf) {
  const std::string path = WriteSnapshot("half", /*second_bin_hit=*/false);
  const std::string src =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"" +
      path +
      "\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(src, "cov"), 50.0);
}

// A snapshot that covered both bins of the loaded covergroup type raises the
// overall coverage $get_coverage() reports to 100.
TEST(Coverage, LoadCoverageDbSyscallThenGetCoverageFull) {
  const std::string path = WriteSnapshot("full", /*second_bin_hit=*/true);
  const std::string src =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"" +
      path +
      "\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(src, "cov"), 100.0);
}

// $load_coverage_db on a file that cannot be opened leaves the live database
// untouched, so $get_coverage() still reports the empty-design value.
TEST(Coverage, LoadCoverageDbSyscallMissingFileIsNoOp) {
  const std::string src =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"/no/such/delta_cov_19_09_missing.txt\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(src, "cov"), 0.0);
}

// $set_coverage_db_name(filename) records, on the run's live coverage database,
// the file name into which coverage is written at the end of the run. The
// recorded name is observed on the context's coverage database after the run.
TEST(Coverage, SetCoverageDbNameSyscallRecordsName) {
  const std::string src =
      "module t;\n"
      "  initial $set_coverage_db_name(\"cov_out.dat\");\n"
      "endmodule\n";
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.CoverageData().CoverageDbName(), "cov_out.dat");
}

// $get_coverage() reports the coverage of *all* covergroup types, so its value
// aggregates across more than one type. Loading a snapshot that holds a fully
// covered type and a half-covered type of equal weight makes $get_coverage()
// report their average, 75, end to end.
TEST(Coverage, GetCoverageSyscallAggregatesAcrossLoadedTypes) {
  std::string path = testing::TempDir() + "delta_cov_19_09_two_types.txt";
  {
    std::ofstream out(path);
    out << "CG cg_a 1\n"
        << "CP x\n"
        << "BIN a0 0 1\n"
        << "BIN a1 1 2\n"  // cg_a: both bins covered -> 100%
        << "CG cg_b 1\n"
        << "CP y\n"
        << "BIN b0 0 1\n"
        << "BIN b1 1 0\n";  // cg_b: one of two bins covered -> 50%
  }
  const std::string src =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"" +
      path +
      "\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(src, "cov"), 75.0);
}

// The file-name argument of $load_coverage_db need not be a string literal: a
// string variable holding the path selects the same snapshot. This exercises
// the variable-argument form through the full pipeline.
TEST(Coverage, LoadCoverageDbSyscallFileNameFromStringVar) {
  const std::string path = WriteSnapshot("half_var", /*second_bin_hit=*/false);
  const std::string src =
      "module t;\n"
      "  string f;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    f = \"" +
      path +
      "\";\n"
      "    $load_coverage_db(f);\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(src, "cov"), 50.0);
}

// The file-name argument of $set_coverage_db_name may likewise be a string
// variable; the name it holds is what gets recorded on the live database.
TEST(Coverage, SetCoverageDbNameSyscallFileNameFromStringVar) {
  const std::string src =
      "module t;\n"
      "  string f;\n"
      "  initial begin\n"
      "    f = \"cov_var.dat\";\n"
      "    $set_coverage_db_name(f);\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.CoverageData().CoverageDbName(), "cov_var.dat");
}

// $load_coverage_db rejects a malformed snapshot the same way it rejects an
// unopenable one: the load aborts before touching the live database, so
// $get_coverage() still reports the empty value. Here the file opens but its
// first record is a bin with no enclosing covergroup.
TEST(Coverage, LoadCoverageDbSyscallMalformedFileIsNoOp) {
  std::string path = testing::TempDir() + "delta_cov_19_09_malformed.txt";
  {
    std::ofstream out(path);
    out << "BIN orphan 0 1\n";  // A bin with no preceding CG / CP record.
  }
  const std::string src =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"" +
      path +
      "\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(src, "cov"), 0.0);
}

}  // namespace
