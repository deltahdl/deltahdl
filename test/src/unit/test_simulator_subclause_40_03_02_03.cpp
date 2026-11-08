#include <gtest/gtest.h>

#include <cstdint>
#include <limits>
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

constexpr int kAssertion = 20;
constexpr int kToggle = 23;

constexpr int kError = static_cast<int>(CoverageStatus::kError);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);
constexpr int kOverflow = static_cast<int>(CoverageStatus::kOverflow);

constexpr std::string_view kScope = "$root.tb.unit1";

constexpr int kModule = 10;
constexpr int kHier = 11;

int RunGet(SimFixture& f, int coverage_type, int scope_def,
           std::string_view scope) {
  auto* call = MkSysCall(f.arena, "$coverage_get",
                         {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
                          MkInt(f.arena, static_cast<uint64_t>(scope_def)),
                          MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

constexpr int kResetControl = 2;

void RunControl(SimFixture& f, int control, std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, static_cast<uint64_t>(control)), MkInt(f.arena, kToggle),
       MkInt(f.arena, kHier), MkStr(f.arena, scope)});
  EvalExpr(call, f.ctx, f.arena);
}

TEST(CoverageGet, ReportsCurrentCoveredCountPerType) {
  SimFixture f;
  Cov(f).SetCoveredItems(std::string(kScope), kToggle, 12);
  Cov(f).SetCoveredItems(std::string(kScope), kAssertion, 3);

  EXPECT_EQ(RunGet(f, kToggle, kHier, kScope), 12);
  EXPECT_EQ(RunGet(f, kAssertion, kHier, kScope), 3);
}

TEST(CoverageGet, ReportsCoveredCountDistinctFromMaximum) {
  SimFixture f;
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);
  Cov(f).SetCoveredItems(std::string(kScope), kToggle, 30);

  EXPECT_EQ(RunGet(f, kToggle, kHier, kScope), 30);
}

TEST(CoverageGet, NoCoveredItemsReportsNoCoverage) {
  SimFixture f;
  Cov(f).SetCoveredItems(std::string(kScope), kToggle, 12);

  EXPECT_EQ(RunGet(f, kAssertion, kHier, kScope), kNoCov);
}

TEST(CoverageGet, UnknownScopeIsBadArgument) {
  SimFixture f;
  EXPECT_EQ(RunGet(f, kToggle, kHier, "$root.tb.nonesuch"), kError);
}

TEST(CoverageGet, CountExceedingIntegerRangeOverflows) {
  SimFixture f;
  Cov(f).SetCoveredItems(
      std::string(kScope), kToggle,
      static_cast<std::int64_t>(std::numeric_limits<std::int32_t>::max()) + 1);

  EXPECT_EQ(RunGet(f, kToggle, kHier, kScope), kOverflow);
}

TEST(CoverageGet, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_get", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

TEST(CoverageGet, TheScopeDefinitionDecidesWhatIsSummed) {
  SimFixture f;
  Cov(f).SetCoveredItems("top.dut", kToggle, 5);
  Cov(f).SetCoveredItems("top.dut.u1", kToggle, 3);
  Cov(f).SetCoveredItems("top.dut.u1.leaf", kToggle, 1);
  Cov(f).SetCoveredItems("top.other", kToggle, 100);

  EXPECT_EQ(RunGet(f, kToggle, kHier, "top.dut"), 9);
  EXPECT_EQ(RunGet(f, kToggle, kModule, "top.dut"), 5);
}

TEST(CoverageGet, ADefinitionNameSumsOverEveryInstanceOfThatModule) {
  SimFixture f;
  Cov(f).SetCoveredItems("top.u1", kToggle, 2);
  Cov(f).SetModuleDefinition("top.u1", "leaf");
  Cov(f).SetCoveredItems("top.u2", kToggle, 4);
  Cov(f).SetModuleDefinition("top.u2", "leaf");
  Cov(f).SetCoveredItems("top.u2.inner", kToggle, 8);
  Cov(f).SetModuleDefinition("top.u2.inner", "other");

  EXPECT_EQ(RunGet(f, kToggle, kHier, "leaf"), 14);
  EXPECT_EQ(RunGet(f, kToggle, kModule, "leaf"), 6);
}

TEST(CoverageGet, ResettingCoverageClearsTheCurrentValue) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", kToggle, CoverageAvailability::kFull);
  Cov(f).SetCoveredItems("top.dut", kToggle, 5);
  Cov(f).SetCoveredItems("top.dut.u1", kToggle, 3);
  Cov(f).SetCoveredItems("top.other", kToggle, 100);
  EXPECT_EQ(RunGet(f, kToggle, kHier, "top.dut"), 8);

  RunControl(f, kResetControl, "top.dut");

  EXPECT_EQ(RunGet(f, kToggle, kHier, "top.dut"), kNoCov);
  EXPECT_EQ(RunGet(f, kToggle, kModule, "top.dut"), kNoCov);
  EXPECT_EQ(RunGet(f, kToggle, kHier, "top.other"), 100);
}

TEST(CoverageGet, ResettingTheCurrentValueLeavesTheMaximumStanding) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);
  Cov(f).SetCoveredItems(std::string(kScope), kToggle, 30);

  RunControl(f, kResetControl, kScope);

  EXPECT_EQ(RunGet(f, kToggle, kHier, kScope), kNoCov);
  EXPECT_EQ(Cov(f).CoverageMax(std::string(kScope), kToggle), 48);
}

}  // namespace
