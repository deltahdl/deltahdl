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

int RunSave(SimFixture& f, int coverage_type, std::string_view name) {
  return RunCoverageSysCall(f, "$coverage_save", coverage_type, name);
}

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

TEST(CoverageSave, AvailableTypeIsSavedAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunSave(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 1u);
}

TEST(CoverageSave, SavedDataAreRetrievableByMergeWithTheSameName) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetCoveredItems("top.dut", kToggle, 6);
  Cov(f).SetCoveredItems("top.dut.u1", kToggle, 4);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);
  Cov(f).Control(CoverageControl::kReset, kToggle, "top.dut");
  ASSERT_EQ(Cov(f).CoverageGet("top.dut", kToggle), kNoCov);

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).MergeCount(std::string(kName)), 1u);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle, false), 6);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle), 10);
}

TEST(CoverageSave, TheEntryHoldsTheCoverageAsItStoodAtTheSave) {
  SimFixture f;
  const std::string kScope = "top.dut";
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetCoveredItems(kScope, kToggle, 6);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);

  Cov(f).SetCoveredItems(kScope, kToggle, 9);
  Cov(f).Control(CoverageControl::kReset, kToggle, kScope);

  ASSERT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).CoverageGet(kScope, kToggle), 6);
}

TEST(CoverageSave, SavesOnlyTheCoverageTypeTheCallNames) {
  SimFixture f;
  const std::string kScope = "top.dut";
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetCoveredItems(kScope, kToggle, 6);
  Cov(f).SetCoveredItems(kScope, kAssertion, 3);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);
  Cov(f).Control(CoverageControl::kReset, kToggle, kScope);
  Cov(f).Control(CoverageControl::kReset, kAssertion, kScope);

  EXPECT_EQ(RunMerge(f, kAssertion, kName), kNoCov);
  ASSERT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).CoverageGet(kScope, kAssertion), kNoCov);
  EXPECT_EQ(Cov(f).CoverageGet(kScope, kToggle), 6);
}

TEST(CoverageSave, UnavailableTypeReportsNoCoverageAndSavesNothing) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunSave(f, kAssertion, kName), kNoCov);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 0u);
  EXPECT_EQ(RunMerge(f, kAssertion, kName), kError);
}

TEST(CoverageSave, ErrorRemovesTheEntryForTheName) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);
  ASSERT_EQ(RunMerge(f, kToggle, kName), kOk);

  Cov(f).SetCoverageSaveShouldFail(true);
  EXPECT_EQ(RunSave(f, kToggle, kName), kError);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 0u);
  EXPECT_EQ(RunMerge(f, kToggle, kName), kError);
}

TEST(CoverageSave, OverwritingAnExistingNameIsNotAnError) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);

  EXPECT_EQ(RunSave(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 2u);
}

TEST(CoverageSave, SavingDoesNotAffectCollectionState) {
  SimFixture f;
  const std::string kScope = "top";
  Cov(f).SetAvailability(kScope, kToggle, CoverageAvailability::kFull);
  Cov(f).Control(CoverageControl::kStart, kToggle, kScope);
  Cov(f).SetCoveredItems(kScope, kToggle, 7);

  const bool kCollectingBefore = Cov(f).IsCollecting(kScope, kToggle);
  const auto kStartsBefore = Cov(f).StartCount(kScope, kToggle);
  const int kLevelBefore = Cov(f).CoverageGet(kScope, kToggle);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);

  EXPECT_EQ(Cov(f).IsCollecting(kScope, kToggle), kCollectingBefore);
  EXPECT_EQ(Cov(f).StartCount(kScope, kToggle), kStartsBefore);
  EXPECT_EQ(Cov(f).CoverageGet(kScope, kToggle), kLevelBefore);
}

TEST(CoverageSave, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_save", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

std::string FsmSaveDesign(const std::string& body) {
  return "module top;\n"
         "  parameter [1:0] /* tool enum s_e */ P = 0, Q = 1, R = 2;\n"
         "  /* tool state_vector cur enum s_e */\n"
         "  logic [1:0] cur;\n"
         "  string db;\n"
         "  int r1, r2, r3;\n"
         "  initial begin\n"
         "    cur = Q; #1\n" +
         body +
         "    $display(\"%0d %0d %0d\", r1, r2, r3);\n"
         "  end\n"
         "endmodule\n";
}

TEST(CoverageSave, CoverageTheDesignCollectedIsThereToSave) {
  SimFixture f;
  const std::string kOut = RunCapture(
      FsmSaveDesign("    r1 = $coverage_save(21, \"fsm.cov\");\n"
                    "    r2 = $coverage_merge(21, \"fsm.cov\");\n"
                    "    r3 = $coverage_control(3, 20, 10, \"top\");\n"
                    "    r3 = $coverage_save(20, \"none.cov\");\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1 1 0\n");
}

TEST(CoverageSave, AStringVariableNamesTheDatabase) {
  SimFixture f;
  const std::string kOut =
      RunCapture(FsmSaveDesign("    db = \"var.cov\";\n"
                               "    r1 = $coverage_save(21, db);\n"
                               "    r2 = $coverage_merge(21, \"var.cov\");\n"
                               "    r3 = $coverage_merge(21, \"\");\n"),
                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1 1 -1\n");
}

void KeepDatabasesIn(SimFixture& f, const ScratchDir& scratch) {
  Cov(f).SetDatabaseDirectory(scratch.dir.string());
  Cov(f).SetModuleDefinition("top", "top");
  Cov(f).SetAvailability("top", kToggle, CoverageAvailability::kFull);
}

TEST(CoverageSave, ASavedDatabaseOutlivesTheRunThatSavedIt) {
  ScratchDir scratch;
  {
    SimFixture first;
    KeepDatabasesIn(first, scratch);
    Cov(first).SetCoveredItems("top", kToggle, 6);
    Cov(first).SetCoveredItems("top.inner", kToggle, 1);
    ASSERT_EQ(RunSave(first, kToggle, kName), kOk);
  }
  SimFixture later;
  KeepDatabasesIn(later, scratch);

  EXPECT_EQ(RunMerge(later, kToggle, kName), kOk);
  EXPECT_EQ(Cov(later).CoverageGet("top", kToggle, false), 6);
  EXPECT_EQ(Cov(later).CoverageGet("top", kToggle), 7);
}

TEST(CoverageSave, ADatabaseThatCannotBeWrittenIsAnError) {
  ScratchDir scratch;
  SimFixture f;
  KeepDatabasesIn(f, scratch);
  Cov(f).SetDatabaseDirectory((scratch.dir / "absent").string());

  EXPECT_EQ(RunSave(f, kToggle, kName), kError);
  EXPECT_EQ(RunMerge(f, kToggle, kName), kError);
}

TEST(CoverageSave, AFailedSaveRemovesTheDatabaseFile) {
  ScratchDir scratch;
  SimFixture f;
  KeepDatabasesIn(f, scratch);
  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);
  ASSERT_TRUE(std::filesystem::exists(scratch.dir / std::string(kName)));

  Cov(f).SetCoverageSaveShouldFail(true);
  EXPECT_EQ(RunSave(f, kToggle, kName), kError);
  EXPECT_FALSE(std::filesystem::exists(scratch.dir / std::string(kName)));
}

}  // namespace
