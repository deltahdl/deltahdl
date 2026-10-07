#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// LRM 19.9 with 19.11.1: the coverage a database loaded for covergroup type
// cg adds its bin counts to the live instance's bins of the same name, so
// $get_coverage reads b0 from the run and b1 from the load, 100, while the
// live instance keeps the half it sampled and its own sample count. Averaged
// with the loaded record as one more instance, it read 50.
TEST(Coverage, LoadedCoverageAddsItsBinCountsToTheLiveInstance) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->type_name = "cg";
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);
  CoverBin b1;
  b1.name = "b1";
  b1.values = {1};
  CoverageDB::AddBin(cp, b1);
  db.Sample(g, {{"x", 0}});

  CoverGroup loaded;
  loaded.name = "cg";
  loaded.type_name = "cg";
  loaded.sample_count = 1;
  CoverPoint lcp;
  lcp.name = "x";
  CoverBin lb0;
  lb0.name = "b0";
  lb0.values = {0};
  lcp.bins.push_back(lb0);
  CoverBin lb1 = lb0;
  lb1.name = "b1";
  lb1.values = {1};
  lb1.hit_count = 1;
  lcp.bins.push_back(lb1);
  loaded.coverpoints.push_back(lcp);

  db.MergeCumulativeCoverage({loaded});

  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 100.0);
  EXPECT_EQ(db.FindGroup("cg")->sample_count, 1u);
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(db.FindGroup("cg")), 50.0);
  ASSERT_NE(db.LoadedCoverageOf("cg"), nullptr);
}

// LRM 19.9, 19.11.3: the records a database holds of one covergroup type, and
// those a second load brings, are one cumulative coverage of the type: an item
// and a bin are matched by name, a matched bin's counts and the sample counts
// summed, and a bin or item that matches none kept as it is.
TEST(Coverage, LoadedRecordsOfOneTypeUniteByName) {
  CoverageDB db;
  CoverGroup first;
  first.name = "g";
  first.type_name = "cg";
  first.sample_count = 1;
  CoverPoint x;
  x.name = "x";
  CoverBin b0;
  b0.name = "b0";
  b0.hit_count = 1;
  x.bins.push_back(b0);
  first.coverpoints.push_back(x);
  CoverGroup second = first;
  second.name = "h";
  second.sample_count = 2;
  second.coverpoints[0].bins[0].hit_count = 2;
  CoverBin b1;
  b1.name = "b1";
  b1.hit_count = 4;
  second.coverpoints[0].bins.push_back(b1);
  CoverPoint y;
  y.name = "y";
  second.coverpoints.push_back(y);
  CrossCover xy;
  xy.name = "xy";
  CrossBin cb;
  cb.name = "cb";
  cb.hit_count = 5;
  xy.bins.push_back(cb);
  second.crosses.push_back(xy);
  CoverGroup third = second;
  third.coverpoints.clear();

  db.MergeCumulativeCoverage({first, second});
  db.MergeCumulativeCoverage({third});

  const CoverGroup* cumulative = db.LoadedCoverageOf("cg");
  ASSERT_NE(cumulative, nullptr);
  EXPECT_EQ(cumulative->sample_count, 5u);
  ASSERT_EQ(cumulative->coverpoints.size(), 2u);
  ASSERT_EQ(cumulative->coverpoints[0].bins.size(), 2u);
  EXPECT_EQ(cumulative->coverpoints[0].bins[0].hit_count, 3u);
  EXPECT_EQ(cumulative->coverpoints[0].bins[1].hit_count, 4u);
  EXPECT_EQ(cumulative->coverpoints[1].name, "y");
  ASSERT_EQ(cumulative->crosses.size(), 1u);
  EXPECT_EQ(cumulative->crosses[0].bins.at(0).hit_count, 10u);
}

// LRM 19.9: a loaded record that names no covergroup type joins no other
// record, and no live instance that names none either, so $get_coverage
// averages the live instance's 0 with each record's 100.
TEST(Coverage, ALoadedRecordOfNoTypeStandsAlone) {
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
  CoverBin lb0 = b0;
  lb0.hit_count = 1;
  lcp.bins.push_back(lb0);
  loaded.coverpoints.push_back(lcp);
  CoverGroup again = loaded;

  db.MergeCumulativeCoverage({loaded, again});

  EXPECT_EQ(db.LoadedCoverageOf(""), nullptr);
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 200.0 / 3.0);
}

// LRM 19.9: a covergroup type present only in the loaded cumulative coverage
// is held as the loaded coverage of it, built as no live group, and is saved
// again with the run's coverage, which a later run loads as cumulative.
TEST(Coverage, LoadCumulativeCoverageAddsAbsentType) {
  CoverageDB db;
  CoverGroup loaded;
  loaded.name = "cg2";
  loaded.type_name = "cg2";
  loaded.sample_count = 3;
  db.MergeCumulativeCoverage({loaded});

  EXPECT_EQ(db.GroupCount(), 0u);
  ASSERT_NE(db.LoadedCoverageOf("cg2"), nullptr);
  EXPECT_EQ(db.LoadedCoverageOf("cg2")->sample_count, 3u);
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_resave.db";
  db.SaveCoverageDbFile(kPath);
  std::ifstream in(kPath);
  std::stringstream text;
  text << in.rdbuf();
  EXPECT_EQ(text.str(), "CG cg2 3\nTY cg2\n");
  std::remove(kPath.c_str());
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

// LRM 19.11: get_inst_coverage() is the coverage of the instance alone, so a
// loaded record of the same name adds no coverpoint, bin or cross hit to the
// live instance, and keeps its own items whole.
TEST(Coverage, LoadCumulativeCoverageLeavesTheLiveInstanceAsItWas) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "x");
  CrossCover live_cross;
  live_cross.name = "xy";
  CrossBin live_bin;
  live_bin.name = "cb";
  live_bin.hit_count = 1;
  live_cross.bins.push_back(live_bin);
  CoverageDB::AddCross(g, live_cross);

  CoverGroup loaded;
  loaded.name = "cg";
  loaded.type_name = "cg";
  CoverPoint lcp;
  lcp.name = "y";
  loaded.coverpoints.push_back(lcp);
  CrossCover loaded_cross = live_cross;
  loaded_cross.bins[0].hit_count = 4;
  loaded.crosses.push_back(loaded_cross);

  db.MergeCumulativeCoverage({loaded});

  auto* live = db.FindGroup("cg");
  ASSERT_EQ(live->coverpoints.size(), 1u);
  EXPECT_EQ(live->crosses.at(0).bins.at(0).hit_count, 1u);
  const CoverGroup* kept = db.LoadedCoverageOf("cg");
  ASSERT_NE(kept, nullptr);
  EXPECT_EQ(kept->coverpoints.at(0).name, "y");
  EXPECT_EQ(kept->crosses.at(0).bins.at(0).hit_count, 4u);
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
// types, so a single load can touch more than one type at once, each record
// the loaded coverage of its own type beside the live instances.
TEST(Coverage, LoadCumulativeCoverageHandlesMultipleTypes) {
  CoverageDB db;
  auto* a = db.CreateGroup("cg_a");
  a->sample_count = 1;
  auto* b = db.CreateGroup("cg_b");
  b->sample_count = 2;

  CoverGroup la;
  la.name = "cg_a";
  la.type_name = "cg_a";
  la.sample_count = 10;
  CoverGroup lb;
  lb.name = "cg_b";
  lb.type_name = "cg_b";
  lb.sample_count = 20;
  db.MergeCumulativeCoverage({la, lb});

  EXPECT_EQ(db.FindGroup("cg_a")->sample_count, 1u);
  EXPECT_EQ(db.FindGroup("cg_b")->sample_count, 2u);
  ASSERT_NE(db.LoadedCoverageOf("cg_a"), nullptr);
  ASSERT_NE(db.LoadedCoverageOf("cg_b"), nullptr);
  EXPECT_EQ(db.LoadedCoverageOf("cg_a")->sample_count, 10u);
  EXPECT_EQ(db.LoadedCoverageOf("cg_b")->sample_count, 20u);
}

// --- LRM 19.9: the predefined coverage system tasks/functions driven from real
// source through the full pipeline (parse, elaborate, lower, run). These
// observe the production dispatch that wires $get_coverage / $load_coverage_db
// / $set_coverage_db_name to the run's live coverage database.
// -----------------

// $get_coverage() is a system function returning the overall coverage of all
// coverage group types as a real in the range 0 to 100, computed as §19.11
// describes. That computation names this case explicitly: $get_coverage returns
// 100.0 for a design holding no covergroup instance. The empty design is the
// fully-covered case, not the uncovered one, because a coverpoint contributing
// no bins leaves a zero denominator and is excluded from the calculation rather
// than counted as a miss.
TEST(Coverage, GetCoverageSyscallEmptyDesignReturnsOneHundred) {
  const std::string kSrc =
      "module t;\n"
      "  real cov;\n"
      "  initial cov = $get_coverage();\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 100.0);
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
  const std::string kPath = WriteSnapshot("half", /*second_bin_hit=*/false);
  const std::string kSrc =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"" +
      kPath +
      "\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 50.0);
}

// A snapshot that covered both bins of the loaded covergroup type raises the
// overall coverage $get_coverage() reports to 100.
TEST(Coverage, LoadCoverageDbSyscallThenGetCoverageFull) {
  const std::string kPath = WriteSnapshot("full", /*second_bin_hit=*/true);
  const std::string kSrc =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"" +
      kPath +
      "\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 100.0);
}

// $load_coverage_db on a file that cannot be opened leaves the live database
// untouched, so $get_coverage() still reports the empty-design value, which
// §19.11 fixes at 100.0 for a design with no covergroup instances.
TEST(Coverage, LoadCoverageDbSyscallMissingFileIsNoOp) {
  const std::string kSrc =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"/no/such/delta_cov_19_09_missing.txt\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 100.0);
}

// $set_coverage_db_name(filename) records, on the run's live coverage database,
// the file name into which coverage is written at the end of the run. The
// recorded name is observed on the context's coverage database after the run.
TEST(Coverage, SetCoverageDbNameSyscallRecordsName) {
  const std::string kSrc =
      "module t;\n"
      "  initial $set_coverage_db_name(\"cov_out.dat\");\n"
      "endmodule\n";
  SimFixture f;
  auto* design = ElaborateSrc(kSrc, f);
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
  const std::string kSrc =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"" +
      path +
      "\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 75.0);
}

// The file-name argument of $load_coverage_db need not be a string literal: a
// string variable holding the path selects the same snapshot. This exercises
// the variable-argument form through the full pipeline.
TEST(Coverage, LoadCoverageDbSyscallFileNameFromStringVar) {
  const std::string kPath = WriteSnapshot("half_var", /*second_bin_hit=*/false);
  const std::string kSrc =
      "module t;\n"
      "  string f;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    f = \"" +
      kPath +
      "\";\n"
      "    $load_coverage_db(f);\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 50.0);
}

// The file-name argument of $set_coverage_db_name may likewise be a string
// variable; the name it holds is what gets recorded on the live database.
TEST(Coverage, SetCoverageDbNameSyscallFileNameFromStringVar) {
  const std::string kSrc =
      "module t;\n"
      "  string f;\n"
      "  initial begin\n"
      "    f = \"cov_var.dat\";\n"
      "    $set_coverage_db_name(f);\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto* design = ElaborateSrc(kSrc, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.CoverageData().CoverageDbName(), "cov_var.dat");
}

// $load_coverage_db rejects a malformed snapshot the same way it rejects an
// unopenable one: the load aborts before touching the live database, so
// $get_coverage() still reports the empty value of 100.0 that §19.11 fixes for
// a design with no covergroup instances. Here the file opens but its first
// record is a bin with no enclosing covergroup.
TEST(Coverage, LoadCoverageDbSyscallMalformedFileIsNoOp) {
  std::string path = testing::TempDir() + "delta_cov_19_09_malformed.txt";
  {
    std::ofstream out(path);
    out << "BIN orphan 0 1\n";  // A bin with no preceding CG / CP record.
  }
  const std::string kSrc =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"" +
      path +
      "\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 100.0);
}

// The text of the file at `path`, empty where there is none.
static std::string FileText(const std::string& path) {
  std::ifstream in(path);
  std::stringstream text;
  text << in.rdbuf();
  return text.str();
}

// A module whose covergroup cg declares `items` and is sampled by `sample`
// with the bits a and b, whose initial block runs `body`.
static std::string CovergroupRun(const std::string& items,
                                 const std::string& body) {
  return "module t;\n"
         "  covergroup cg with function sample(bit [1:0] a, bit b);\n" +
         items +
         "  endgroup\n"
         "  cg c = new;\n"
         "  initial begin\n" +
         body +
         "  end\n"
         "endmodule\n";
}

// §19.9: $set_coverage_db_name names the file the run's coverage is saved to
// at its end, and $load_coverage_db in a later run loads it as cumulative
// coverage: the first run hits bins 0 and 1 of cp and the transition 0 => 1 of
// ct, and the second only bin 2, so the live instance's bins with the loaded
// counts added hold three of cp's four bins and ct's one, 87.5. The end of a
// run (main.cpp, after the final blocks) saves the database; no file was
// written, and the second run read only its own hit, 12.5.
TEST(Coverage, TheRunSavesItsDatabaseForALaterRunToLoad) {
  const std::string kPath =
      testing::TempDir() + "delta_cov_19_09_round_trip.db";
  const std::string kItems =
      "    cp: coverpoint a;\n"
      "    ct: coverpoint a { bins t = (0 => 1); }\n";
  std::remove(kPath.c_str());
  SimFixture first;
  RunCapture(CovergroupRun(kItems, "    $set_coverage_db_name(\"" + kPath +
                                       "\");\n"
                                       "    c.sample(0, 0); c.sample(1, 0);\n"),
             first);
  first.ctx.CoverageData().SaveNamedCoverageDb();
  const std::string kSaved = FileText(kPath);
  SimFixture second;
  EXPECT_EQ(
      RunCapture(CovergroupRun(kItems, "    $load_coverage_db(\"" + kPath +
                                           "\");\n    c.sample(2, 0);\n"
                                           "    $display(\"%0.2f %0.2f\", "
                                           "$get_coverage(), "
                                           "cg::get_coverage());\n"),
                 second),
      "87.50 87.50\n");
  // The second run named no database, so its end writes none over the first.
  second.ctx.CoverageData().SaveNamedCoverageDb();
  EXPECT_EQ(FileText(kPath), kSaved);
  std::remove(kPath.c_str());
}

// §19.9 with §19.6: the database holds a covergroup's crosses as well as its
// coverpoints, so the cross x of the second run, which hits none of its four
// bins, reads the one the first run hit, 25. The file held no cross, and the
// type's cross read the live one's 0.
TEST(Coverage, TheSavedDatabaseCarriesCrossBinHits) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_cross.db";
  const std::string kItems =
      "    ca: coverpoint a { bins lo = {0}; bins hi = {[1:3]}; }\n"
      "    cb: coverpoint b;\n"
      "    x: cross ca, cb;\n";
  std::remove(kPath.c_str());
  SimFixture first;
  RunCapture(CovergroupRun(kItems, "    $set_coverage_db_name(\"" + kPath +
                                       "\");\n    c.sample(0, 0);\n"),
             first);
  first.ctx.CoverageData().SaveNamedCoverageDb();
  SimFixture second;
  EXPECT_EQ(
      RunCapture(CovergroupRun(kItems, "    $load_coverage_db(\"" + kPath +
                                           "\");\n"
                                           "    $display(\"%0.2f\", "
                                           "cg::x::get_coverage());\n"),
                 second),
      "25.00\n");
  std::remove(kPath.c_str());
}

// Loads a database holding `record` into a run of CovergroupRun whose cg
// covers a in its four automatic bins, samples 0 and prints the type's
// coverage, returning what the run printed.
static std::string LoadRecordThenSample(const std::string& record) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_bad.db";
  {
    std::ofstream out(kPath);
    out << record;
  }
  SimFixture f;
  std::string printed =
      RunCapture(CovergroupRun("    cp: coverpoint a;\n",
                               "    $load_coverage_db(\"" + kPath +
                                   "\");\n    c.sample(0, 0);\n"
                                   "    $display(\"%0.2f\", "
                                   "cg::get_coverage());\n"),
                 f);
  std::remove(kPath.c_str());
  return printed;
}

// §19.9: a snapshot whose cross record or cross bin stands where no
// covergroup or cross encloses it is malformed, and loading it leaves the
// live database as it was: cg's one bin of four stays the only one covered.
TEST(Coverage, ACrossRecordOutsideItsEnclosingRecordFailsTheLoad) {
  for (const std::string kRecord :
       {"CR x\n", "CG t.c 1\nXBIN <lo,auto[0]> 1\n", "CG t.c 1\nCR\n",
        "CG t.c 1\nCR x\nXBIN b\n"}) {
    EXPECT_EQ(LoadRecordThenSample(kRecord), "25.00\n") << kRecord;
  }
}

// §19.9: a type record with no instance record before it, or with no type
// name, is malformed, and loading it leaves the live database as it was.
TEST(Coverage, ATypeRecordOutsideAnInstanceRecordFailsTheLoad) {
  for (const std::string kRecord : {"TY cg\n", "CG g 1\nTY"}) {
    EXPECT_EQ(LoadRecordThenSample(kRecord), "25.00\n") << kRecord;
  }
}

// §19.9: the saved database is the form LoadCoverageDbFile reads, a bin's
// first value standing for it and 0 where it lists none, its spans held as
// ranges instead.
TEST(Coverage, SaveCoverageDbFileWritesTheLoadedForm) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {5};
  CoverageDB::AddBin(cp, b0);
  CoverBin b1;
  b1.name = "b1";
  CoverageDB::AddBin(cp, b1);
  db.Sample(g, {{"x", 5}});
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_form.db";
  db.SaveCoverageDbFile(kPath);
  EXPECT_EQ(FileText(kPath), "CG cg 1\nCP x\nBIN b0 5 1\nBIN b1 0 0\n");
  std::remove(kPath.c_str());
}

// A module whose covergroup cg, its type options `options` first, covers x in
// bins b1 and b2, with one instance named `inst` and an initial block running
// `body`.
static std::string InstanceRun(const std::string& inst,
                               const std::string& options,
                               const std::string& body) {
  return "module t;\n"
         "  bit [1:0] x;\n"
         "  covergroup cg;\n" +
         options +
         "    px: coverpoint x { bins b1 = {1}; bins b2 = {2}; }\n"
         "  endgroup\n"
         "  cg " +
         inst +
         " = new;\n"
         "  initial begin\n" +
         body +
         "  end\n"
         "endmodule\n";
}

// Runs InstanceRun with an instance g that covers b1 and saves the run's
// coverage to `path`, then with an instance h that loads it, prints the type's
// coverage, covers b2 and prints `after`, returning what the second run
// printed.
static std::string SaveAsGThenLoadIntoH(const std::string& path,
                                        const std::string& options,
                                        const std::string& after) {
  SimFixture first;
  RunCapture(InstanceRun("g", options,
                         "    $set_coverage_db_name(\"" + path +
                             "\");\n    x = 1; g.sample();\n"),
             first);
  first.ctx.CoverageData().SaveNamedCoverageDb();
  SimFixture second;
  return RunCapture(
      InstanceRun("h", options,
                  "    $load_coverage_db(\"" + path +
                      "\");\n"
                      "    $display(\"%0.2f\", cg::get_coverage());\n"
                      "    x = 2; h.sample();\n" +
                      after),
      second);
}

// §19.9, §19.11.1: the database holds the cumulative coverage of covergroup
// types, so what a saved instance g covered, b1, adds to the bin counts of
// type cg whatever instance the run builds: the type reads 50 before the live
// h samples and 100 once it covers b2. h's own coverage is what h sampled.
// Averaged with the loaded g as one more instance, the type read 25, then 50.
TEST(Coverage, LoadedCoverageAddsToTheBinCountsOfItsType) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_inst.db";
  EXPECT_EQ(SaveAsGThenLoadIntoH(kPath, "",
                                 "    $display(\"%0.2f %0.2f\", "
                                 "cg::get_coverage(), "
                                 "h.get_inst_coverage());\n"),
            "50.00\n100.00 50.00\n");
  std::remove(kPath.c_str());
}

// §19.11.3: with merge_instances set, the type's coverage is the union of the
// loaded b1 and the live h's b2, and so is that of its coverpoint
// px; h's get_inst_coverage() returns the same, its get_inst_coverage option
// being off (§19.7, Table 19-1).
TEST(Coverage, LoadedCoverageJoinsTheMergedUnionOfItsType) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_merge.db";
  EXPECT_EQ(
      SaveAsGThenLoadIntoH(kPath, "    type_option.merge_instances = 1;\n",
                           "    $display(\"%0.2f %0.2f %0.2f\", "
                           "cg::get_coverage(), "
                           "cg::px::get_coverage(), "
                           "h.get_inst_coverage());\n"),
      "50.00\n100.00 100.00 100.00\n");
  std::remove(kPath.c_str());
}

// §19.9: the saved database names the covergroup type of each instance, in a
// TY record after the instance's CG record.
TEST(Coverage, SavedInstanceRecordsItsCovergroupType) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_type.db";
  SimFixture f;
  RunCapture(InstanceRun("g", "", "    x = 1; g.sample();\n"), f);
  f.ctx.CoverageData().SaveCoverageDbFile(kPath);
  EXPECT_EQ(FileText(kPath).substr(0, 14), "CG g 1\nTY cg\nC");
  std::remove(kPath.c_str());
}

// Saves a run of InstanceRun whose instance g covers b1 to `path`, the
// probe's first run.
static void SaveGCoveringB1(const std::string& path) {
  SimFixture first;
  RunCapture(InstanceRun("g", "",
                         "    $set_coverage_db_name(\"" + path +
                             "\");\n    x = 1; g.sample();\n"),
             first);
  first.ctx.CoverageData().SaveNamedCoverageDb();
}

// §19.11: get_inst_coverage() is the coverage of the instance alone, so a g
// built before the load, named as the saved g is, reads the half it sampled,
// b2, while the type reads b1 from the load and b2 from the run, 100. The
// loaded counts were merged into the live g, which read 100.
TEST(Coverage, ALoadedRecordStaysOutOfTheInstanceBuiltBeforeIt) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_before.db";
  SaveGCoveringB1(kPath);
  SimFixture second;
  EXPECT_EQ(RunCapture(InstanceRun("g", "",
                                   "    $load_coverage_db(\"" + kPath +
                                       "\");\n"
                                       "    x = 2; g.sample();\n"
                                       "    $display(\"%0.2f %0.2f\", "
                                       "cg::get_coverage(), "
                                       "g.get_inst_coverage());\n"),
                       second),
            "100.00 50.00\n");
  std::remove(kPath.c_str());
}

// Nothing makes coverage depend on when an instance is built relative to the
// load: a g built after it reads what one built before it does.
TEST(Coverage, BothBuildOrdersReadTheSameCoverage) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_after.db";
  SaveGCoveringB1(kPath);
  SimFixture second;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  bit [1:0] x;\n"
                 "  covergroup cg;\n"
                 "    px: coverpoint x { bins b1 = {1}; bins b2 = {2}; }\n"
                 "  endgroup\n"
                 "  cg g;\n"
                 "  initial begin\n"
                 "    $load_coverage_db(\"" +
                     kPath +
                     "\");\n"
                     "    g = new;\n"
                     "    x = 2; g.sample();\n"
                     "    $display(\"%0.2f %0.2f\", cg::get_coverage(), "
                     "g.get_inst_coverage());\n"
                     "  end\n"
                     "endmodule\n",
                 second),
      "100.00 50.00\n");
  std::remove(kPath.c_str());
}

}  // namespace
