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

TEST(Coverage, LoadCumulativeCoverageEmptyIsNoOp) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "x");
  g->sample_count = 5;

  db.MergeCumulativeCoverage({});

  EXPECT_EQ(db.GroupCount(), 1u);
  EXPECT_EQ(db.FindGroup("cg")->sample_count, 5u);
}

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
  db.Sample(a, {{"x", 1}});

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
  db.Sample(b, {{"y", 0}});

  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 75.0);
}

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

TEST(Coverage, GetCoverageSyscallEmptyDesignReturnsOneHundred) {
  const std::string kSrc =
      "module t;\n"
      "  real cov;\n"
      "  initial cov = $get_coverage();\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 100.0);
}

static std::string WriteSnapshot(const std::string& tag, bool second_bin_hit) {
  std::string path = testing::TempDir() + "delta_cov_19_09_" + tag + ".txt";
  std::ofstream out(path);
  out << "CG cg 1\n"
      << "CP x\n"
      << "BIN b0 0 1\n"
      << "BIN b1 1 " << (second_bin_hit ? "2" : "0") << "\n";
  return path;
}

TEST(Coverage, LoadCoverageDbSyscallThenGetCoverageHalf) {
  const std::string kPath = WriteSnapshot("half", false);
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

TEST(Coverage, LoadCoverageDbSyscallThenGetCoverageFull) {
  const std::string kPath = WriteSnapshot("full", true);
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

TEST(Coverage, GetCoverageSyscallAggregatesAcrossLoadedTypes) {
  std::string path = testing::TempDir() + "delta_cov_19_09_two_types.txt";
  {
    std::ofstream out(path);
    out << "CG cg_a 1\n"
        << "CP x\n"
        << "BIN a0 0 1\n"
        << "BIN a1 1 2\n"
        << "CG cg_b 1\n"
        << "CP y\n"
        << "BIN b0 0 1\n"
        << "BIN b1 1 0\n";
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

TEST(Coverage, LoadCoverageDbSyscallFileNameFromStringVar) {
  const std::string kPath = WriteSnapshot("half_var", false);
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

TEST(Coverage, LoadCoverageDbSyscallMalformedFileIsNoOp) {
  std::string path = testing::TempDir() + "delta_cov_19_09_malformed.txt";
  {
    std::ofstream out(path);
    out << "BIN orphan 0 1\n";
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

static std::string FileText(const std::string& path) {
  std::ifstream in(path);
  std::stringstream text;
  text << in.rdbuf();
  return text.str();
}

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
  second.ctx.CoverageData().SaveNamedCoverageDb();
  EXPECT_EQ(FileText(kPath), kSaved);
  std::remove(kPath.c_str());
}

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

TEST(Coverage, ACrossRecordOutsideItsEnclosingRecordFailsTheLoad) {
  for (const std::string kRecord :
       {"CR x\n", "CG t.c 1\nXBIN <lo,auto[0]> 1\n", "CG t.c 1\nCR\n",
        "CG t.c 1\nCR x\nXBIN b\n"}) {
    EXPECT_EQ(LoadRecordThenSample(kRecord), "25.00\n") << kRecord;
  }
}

TEST(Coverage, ATypeRecordOutsideAnInstanceRecordFailsTheLoad) {
  for (const std::string kRecord : {"TY cg\n", "CG g 1\nTY"}) {
    EXPECT_EQ(LoadRecordThenSample(kRecord), "25.00\n") << kRecord;
  }
}

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

TEST(Coverage, LoadedCoverageAddsToTheBinCountsOfItsType) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_inst.db";
  EXPECT_EQ(SaveAsGThenLoadIntoH(kPath, "",
                                 "    $display(\"%0.2f %0.2f\", "
                                 "cg::get_coverage(), "
                                 "h.get_inst_coverage());\n"),
            "50.00\n100.00 50.00\n");
  std::remove(kPath.c_str());
}

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

TEST(Coverage, SavedInstanceRecordsItsCovergroupType) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_09_type.db";
  SimFixture f;
  RunCapture(InstanceRun("g", "", "    x = 1; g.sample();\n"), f);
  f.ctx.CoverageData().SaveCoverageDbFile(kPath);
  EXPECT_EQ(FileText(kPath).substr(0, 14), "CG g 1\nTY cg\nC");
  std::remove(kPath.c_str());
}

static void SaveGCoveringB1(const std::string& path) {
  SimFixture first;
  RunCapture(InstanceRun("g", "",
                         "    $set_coverage_db_name(\"" + path +
                             "\");\n    x = 1; g.sample();\n"),
             first);
  first.ctx.CoverageData().SaveNamedCoverageDb();
}

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
