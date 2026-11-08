#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

constexpr int kAssertion = 20;
constexpr int kFsmState = 21;
constexpr int kStatement = 22;
constexpr int kToggle = 23;
constexpr int kHier = 11;
constexpr int kStart = 0;

constexpr std::string_view kScope = "top.dut";

int RunControl(SimFixture& f, int control, int coverage_type,
               std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, static_cast<uint64_t>(control)),
       MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
       MkInt(f.arena, static_cast<uint64_t>(kHier)), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

int RunGet(SimFixture& f, int coverage_type, std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_get",
      {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
       MkInt(f.arena, static_cast<uint64_t>(kHier)), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

int RunGetMax(SimFixture& f, int coverage_type, std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_get_max",
      {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
       MkInt(f.arena, static_cast<uint64_t>(kHier)), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

TEST(CoverageApiCriteria, OneInterfaceServesEveryCoverageType) {
  SimFixture f;
  CoverageControlState& cov = f.ctx.GetCoverageControlState();
  cov.SetAvailability(std::string(kScope), kStatement,
                      CoverageAvailability::kFull);
  cov.SetAvailability(std::string(kScope), kToggle,
                      CoverageAvailability::kFull);
  cov.SetCoverableItems(std::string(kScope), kStatement, 40);
  cov.SetCoveredItems(std::string(kScope), kStatement, 10);
  cov.SetCoverableItems(std::string(kScope), kToggle, 8);
  cov.SetCoveredItems(std::string(kScope), kToggle, 2);

  EXPECT_EQ(RunControl(f, kStart, kStatement, kScope),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_EQ(RunControl(f, kStart, kToggle, kScope),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_EQ(RunGetMax(f, kStatement, kScope), 40);
  EXPECT_EQ(RunGetMax(f, kToggle, kScope), 8);
  EXPECT_EQ(RunGet(f, kStatement, kScope), 10);
  EXPECT_EQ(RunGet(f, kToggle, kScope), 2);
}

TEST(CoverageApiCriteria, TheMinimumCoverageTypesAreEachSupported) {
  SimFixture f;
  CoverageControlState& cov = f.ctx.GetCoverageControlState();
  cov.SetCoveredItems(std::string(kScope), kAssertion, 1);
  cov.SetCoveredItems(std::string(kScope), kFsmState, 2);
  cov.SetCoveredItems(std::string(kScope), kStatement, 3);
  cov.SetCoveredItems(std::string(kScope), kToggle, 4);

  EXPECT_EQ(RunGet(f, kAssertion, kScope), 1);
  EXPECT_EQ(RunGet(f, kFsmState, kScope), 2);
  EXPECT_EQ(RunGet(f, kStatement, kScope), 3);
  EXPECT_EQ(RunGet(f, kToggle, kScope), 4);
}

TEST(CoverageApiCriteria, TheVpiSideNamesTheSameMinimumTypes) {
  SimFixture f;
  VpiContext vpi_ctx;
  vpi_ctx.Attach(f.ctx);
  SetGlobalVpiContext(&vpi_ctx);
  for (int coverage_type : {kAssertion, kFsmState, kStatement, kToggle}) {
    f.ctx.GetCoverageControlState().SetAvailability(
        std::string(kScope), coverage_type, CoverageAvailability::kFull);
  }
  VpiHandle dut = vpi_ctx.CreateModule("dut", std::string(kScope));

  for (int coverage_type : {vpiAssertCoverage, vpiFsmStateCoverage,
                            vpiStatementCoverage, vpiToggleCoverage}) {
    EXPECT_EQ(vpi_control(vpiCoverageStart, coverage_type, dut),
              static_cast<int>(CoverageStatus::kOk))
        << "coverage type " << coverage_type;
  }

  SetGlobalVpiContext(nullptr);
}

TEST(CoverageApiCriteria, AnUnknownCoverageTypeBreaksNoExistingUsage) {
  SimFixture f;
  CoverageControlState& cov = f.ctx.GetCoverageControlState();
  cov.SetAvailability(std::string(kScope), kToggle,
                      CoverageAvailability::kFull);
  cov.SetCoveredItems(std::string(kScope), kToggle, 5);
  constexpr int kVendorCoverageType = 99;

  ASSERT_EQ(RunGet(f, kToggle, kScope), 5);
  EXPECT_EQ(RunGet(f, kVendorCoverageType, kScope),
            static_cast<int>(CoverageStatus::kNoCoverage));
  EXPECT_EQ(RunControl(f, kStart, kVendorCoverageType, kScope),
            static_cast<int>(CoverageStatus::kNoCoverage));

  EXPECT_EQ(RunGet(f, kToggle, kScope), 5);
}

TEST(CoverageApiCriteria, ASubhierarchyIsNamedRatherThanEnumerated) {
  SimFixture f;
  CoverageControlState& cov = f.ctx.GetCoverageControlState();
  cov.SetCoveredItems("top.dut", kStatement, 30);
  cov.SetCoveredItems("top.checker", kStatement, 4);

  EXPECT_EQ(RunGet(f, kStatement, "top.dut"), 30);
  EXPECT_EQ(RunGet(f, kStatement, "top.checker"), 4);

  EXPECT_EQ(RunGet(f, kStatement, "top.absent"),
            static_cast<int>(CoverageStatus::kError));
}

}  // namespace
