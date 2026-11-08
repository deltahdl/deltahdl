#include <gtest/gtest.h>

#include <cstdint>
#include <limits>
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

constexpr int kAssertion = 20;
constexpr int kToggle = 23;

constexpr int kStart = 0;
constexpr int kReset = 2;

constexpr int kError = static_cast<int>(CoverageStatus::kError);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);
constexpr int kOverflow = static_cast<int>(CoverageStatus::kOverflow);

constexpr int kModule = 10;
constexpr int kHier = 11;

constexpr std::string_view kScope = "$root.tb.unit1";

int RunGetMax(SimFixture& f, int coverage_type, int scope_def,
              std::string_view scope) {
  auto* call = MkSysCall(f.arena, "$coverage_get_max",
                         {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
                          MkInt(f.arena, static_cast<uint64_t>(scope_def)),
                          MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

void RunControl(SimFixture& f, int control, std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, static_cast<uint64_t>(control)), MkInt(f.arena, kToggle),
       MkInt(f.arena, kHier), MkStr(f.arena, scope)});
  EvalExpr(call, f.ctx, f.arena);
}

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

TEST(CoverageGetMax, ReportsSumOfCoverableItemsPerType) {
  SimFixture f;
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);
  Cov(f).SetCoverableItems(std::string(kScope), kAssertion, 5);

  EXPECT_EQ(RunGetMax(f, kToggle, kHier, kScope), 48);
  EXPECT_EQ(RunGetMax(f, kAssertion, kHier, kScope), 5);
}

TEST(CoverageGetMax, NoCoverableItemsReportsNoCoverage) {
  SimFixture f;
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);

  EXPECT_EQ(RunGetMax(f, kAssertion, kHier, kScope), kNoCov);
}

TEST(CoverageGetMax, UnknownScopeIsBadArgument) {
  SimFixture f;
  EXPECT_EQ(RunGetMax(f, kToggle, kHier, "$root.tb.nonesuch"), kError);
}

TEST(CoverageGetMax, CountExceedingIntegerRangeOverflows) {
  SimFixture f;
  Cov(f).SetCoverableItems(
      std::string(kScope), kToggle,
      static_cast<std::int64_t>(std::numeric_limits<std::int32_t>::max()) + 1);

  EXPECT_EQ(RunGetMax(f, kToggle, kHier, kScope), kOverflow);
}

TEST(CoverageGetMax, MaximumStaysConstantAcrossCollectionChanges) {
  SimFixture f;
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);

  const int kBefore = RunGetMax(f, kToggle, kHier, kScope);
  RunControl(f, kStart, kScope);
  RunControl(f, kReset, kScope);
  const int kAfter = RunGetMax(f, kToggle, kHier, kScope);

  EXPECT_EQ(kBefore, 48);
  EXPECT_EQ(kAfter, kBefore);
}

TEST(CoverageGetMax, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_get_max", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

TEST(CoverageGetMax, TheScopeDefinitionDecidesWhatIsSummed) {
  SimFixture f;
  Cov(f).SetCoverableItems("top.dut", kToggle, 8);
  Cov(f).SetCoverableItems("top.dut.u1", kToggle, 4);

  EXPECT_EQ(RunGetMax(f, kToggle, kHier, "top.dut"), 12);
  EXPECT_EQ(RunGetMax(f, kToggle, kModule, "top.dut"), 8);
}

TEST(CoverageGetMax, ADefinitionNameSumsOverEveryInstanceOfThatModule) {
  SimFixture f;
  Cov(f).SetCoverableItems("top.u1", kToggle, 3);
  Cov(f).SetModuleDefinition("top.u1", "leaf");
  Cov(f).SetCoverableItems("top.u2", kToggle, 5);
  Cov(f).SetModuleDefinition("top.u2", "leaf");
  Cov(f).SetCoverableItems("top.u2.inner", kToggle, 7);
  Cov(f).SetModuleDefinition("top.u2.inner", "other");

  EXPECT_EQ(RunGetMax(f, kToggle, kHier, "leaf"), 15);
  EXPECT_EQ(RunGetMax(f, kToggle, kModule, "leaf"), 8);
  EXPECT_EQ(RunGetMax(f, kToggle, kModule, "other"), 7);
}

TEST(CoverageGetMax, AStringNamingAnInstanceIsReadAsThatInstance) {
  SimFixture f;
  Cov(f).SetCoverableItems("leaf", kToggle, 2);
  Cov(f).SetCoverableItems("top.u1", kToggle, 3);
  Cov(f).SetModuleDefinition("top.u1", "leaf");

  EXPECT_EQ(RunGetMax(f, kToggle, kModule, "leaf"), 2);
}

TEST(CoverageGetMax, AMissingScopeNamesNothingAndIsABadArgument) {
  SimFixture f;
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);

  auto* call = MkSysCall(
      f.arena, "$coverage_get_max",
      {MkInt(f.arena, static_cast<uint64_t>(kToggle)), MkInt(f.arena, kHier)});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

TEST(CoverageGetMax, AFailedQueryIsANegativeInteger) {
  SimFixture f;
  const std::string kOut = PreprocessAndCapture(
      "module top;\n"
      "  initial begin\n"
      "    $display(\"%0d\", $coverage_get_max(`SV_COV_STATEMENT,"
      " `SV_COV_MODULE, \"nosuch\"));\n"
      "    $display(\"%0d\", $coverage_get(`SV_COV_STATEMENT, `SV_COV_MODULE,"
      " \"nosuch\"));\n"
      "    $display(\"%0d\", $coverage_control(`SV_COV_CHECK,"
      " `SV_COV_STATEMENT, `SV_COV_MODULE, \"nosuch\"));\n"
      "    $display(\"%0d\", $coverage_get_max(`SV_COV_STATEMENT,"
      " `SV_COV_MODULE, \"nosuch\") < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "-1\n-1\n-1\n1\n");
}

TEST(CoverageGetMax, AnInstanceOfTheDesignIsAScopeTheQueriesName) {
  SimFixture f;
  const std::string kOut = PreprocessAndCapture(
      "module top;\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    r1 = $coverage_get_max(`SV_COV_STATEMENT, `SV_COV_HIER, \"top\");\n"
      "    r2 = $coverage_get_max(`SV_COV_STATEMENT, `SV_COV_MODULE,"
      " \"nosuch\");\n"
      "    r3 = $coverage_control(`SV_COV_CHECK, `SV_COV_STATEMENT,"
      " `SV_COV_HIER, \"top\");\n"
      "    $display(\"%0d %0d %0d\", r1, r2, r3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "5 -1 1\n");
}

TEST(CoverageGetMax, ADefinitionNameOfTheDesignReachesItsInstances) {
  SimFixture f;
  const std::string kOut = PreprocessAndCapture(
      "module leaf; endmodule\n"
      "module top;\n"
      "  leaf u1(); leaf u2();\n"
      "  initial $display(\"%0d\", $coverage_get_max(`SV_COV_STATEMENT,"
      " `SV_COV_MODULE, \"leaf\"));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "0\n");
}

}  // namespace
