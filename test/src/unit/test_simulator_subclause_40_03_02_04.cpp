#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "helpers_coverage_syscall.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

constexpr int kAssertion = 20;
constexpr int kToggle = 23;

constexpr int kOk = static_cast<int>(CoverageStatus::kOk);
constexpr int kError = static_cast<int>(CoverageStatus::kError);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);

constexpr std::string_view kName = "run.cov";

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

TEST(CoverageMerge, FoundForThisDesignMergesAndReportsOk) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName), true,
                                  {kToggle, kAssertion});

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).MergeCount(std::string(kName)), 1u);
}

TEST(CoverageMerge, FoundButMissingTypeReportsNoCoverage) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName), true, {kToggle});

  EXPECT_EQ(RunMerge(f, kAssertion, kName), kNoCov);
  EXPECT_EQ(Cov(f).MergeCount(std::string(kName)), 0u);
}

TEST(CoverageMerge, UnknownNameReportsError) {
  SimFixture f;
  EXPECT_EQ(RunMerge(f, kToggle, "nonesuch.cov"), kError);
}

TEST(CoverageMerge, DatabaseFromAnotherDesignReportsError) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName), false, {kToggle});

  EXPECT_EQ(RunMerge(f, kToggle, kName), kError);
  EXPECT_EQ(Cov(f).MergeCount(std::string(kName)), 0u);
}

TEST(CoverageMerge, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_merge", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

TEST(CoverageMerge, LoadsTheCoverageDataIntoTheSimulation) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName), true, {kToggle});
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kToggle, 6);
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut.u1", kToggle, 4);

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);

  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle, false), 6);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle), 10);
}

TEST(CoverageMerge, LoadsOnlyTheCoverageTypeTheCallNames) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName), true,
                                  {kToggle, kAssertion});
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kToggle, 6);
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kAssertion, 3);

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);

  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle), 6);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kAssertion), kNoCov);

  EXPECT_EQ(RunMerge(f, kAssertion, kName), kOk);

  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kAssertion), 3);
}

TEST(CoverageMerge, CombinesWithCoverageAlreadyCollected) {
  SimFixture f;
  Cov(f).SetCoveredItems("top.dut", kToggle, 9);
  Cov(f).SetCoveredItems("top.dut.u1", kToggle, 1);
  Cov(f).RegisterCoverageDatabase(std::string(kName), true, {kToggle});
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kToggle, 4);
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut.u1", kToggle, 7);

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);

  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle, false), 9);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut.u1", kToggle), 7);
}

TEST(CoverageMerge, AMergeThatIsNotPerformedLoadsNothing) {
  SimFixture f;
  Cov(f).SetCoverableItems("top.dut", kToggle, 10);
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kToggle, 6);
  Cov(f).RegisterCoverageDatabase(std::string(kName), false, {kToggle});

  EXPECT_EQ(RunMerge(f, kToggle, kName), kError);

  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle), kNoCov);
}

void FindDatabasesIn(SimFixture& f, const ScratchDir& scratch,
                     const std::string& definition) {
  Cov(f).SetDatabaseDirectory(scratch.dir.string());
  Cov(f).SetModuleDefinition("top", definition);
}

TEST(CoverageMerge, ADatabaseFileOfThisDesignIsMerged) {
  ScratchDir scratch;
  scratch.Write(std::string(kName),
                "deltahdl-coverage-database 1\n"
                "instance top top\n"
                "type 23\n"
                "covered top 23 4\n");
  SimFixture f;
  FindDatabasesIn(f, scratch, "top");

  EXPECT_EQ(RunMerge(f, kAssertion, kName), kNoCov);
  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).CoverageGet("top", kToggle), 4);
}

TEST(CoverageMerge, ADatabaseFileOfAnotherDesignIsAnError) {
  ScratchDir scratch;
  scratch.Write(std::string(kName),
                "deltahdl-coverage-database 1\n"
                "instance top top\n"
                "type 23\n");
  SimFixture f;
  FindDatabasesIn(f, scratch, "other");

  EXPECT_EQ(RunMerge(f, kToggle, kName), kError);
}

TEST(CoverageMerge, AFileThatIsNoDatabaseIsAnError) {
  ScratchDir scratch;
  scratch.Write("text.cov", "a note\n");
  scratch.Write("broken.cov", "deltahdl-coverage-database 1\ntype x\n");
  scratch.Write("cut.cov", "deltahdl-coverage-database 1\ncovered top\n");
  SimFixture f;
  FindDatabasesIn(f, scratch, "top");

  EXPECT_EQ(RunMerge(f, kToggle, "text.cov"), kError);
  EXPECT_EQ(RunMerge(f, kToggle, "broken.cov"), kError);
  EXPECT_EQ(RunMerge(f, kToggle, "cut.cov"), kError);
}

TEST(CoverageMerge, AMissingNameIsAnError) {
  SimFixture f;
  auto* empty_name =
      MkSysCall(f.arena, "$coverage_merge", {MkInt(f.arena, kToggle), nullptr});
  auto* no_name =
      MkSysCall(f.arena, "$coverage_merge", {MkInt(f.arena, kToggle)});
  EXPECT_EQ(
      static_cast<int32_t>(EvalExpr(empty_name, f.ctx, f.arena).ToUint64()),
      kError);
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(no_name, f.ctx, f.arena).ToUint64()),
            kError);
}

}  // namespace
