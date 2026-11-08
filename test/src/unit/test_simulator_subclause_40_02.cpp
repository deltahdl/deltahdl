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

constexpr std::string_view kScope = "top.dut";
constexpr int kToggle = 23;
constexpr int kHier = 11;

int RunControl(SimFixture& f, int control, std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, static_cast<uint64_t>(control)),
       MkInt(f.arena, static_cast<uint64_t>(kToggle)),
       MkInt(f.arena, static_cast<uint64_t>(kHier)), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

int RunGet(SimFixture& f, std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_get",
      {MkInt(f.arena, static_cast<uint64_t>(kToggle)),
       MkInt(f.arena, static_cast<uint64_t>(kHier)), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

TEST(CoverageApiOverview, TheLanguageDrivesCoverageOnItsOwn) {
  SimFixture f;
  f.ctx.GetCoverageControlState().SetAvailability(std::string(kScope), kToggle,
                                                  CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, 0, kScope), static_cast<int>(CoverageStatus::kOk));
  EXPECT_TRUE(f.ctx.GetCoverageControlState().IsCollecting(std::string(kScope),
                                                           kToggle));

  f.ctx.GetCoverageControlState().SetCoveredItems(std::string(kScope), kToggle,
                                                  7);
  EXPECT_EQ(RunGet(f, kScope), 7);
}

TEST(CoverageApiOverview, TheVpiExtensionStartsTheRunsOwnCoverage) {
  SimFixture f;
  VpiContext vpi_ctx;
  vpi_ctx.Attach(f.ctx);
  SetGlobalVpiContext(&vpi_ctx);

  f.ctx.GetCoverageControlState().SetAvailability(std::string(kScope), kToggle,
                                                  CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx.CreateModule("dut", std::string(kScope));

  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiToggleCoverage, dut),
            static_cast<int>(CoverageStatus::kOk));

  EXPECT_TRUE(f.ctx.GetCoverageControlState().IsCollecting(std::string(kScope),
                                                           kToggle));
  f.ctx.GetCoverageControlState().SetCoveredItems(std::string(kScope), kToggle,
                                                  4);
  EXPECT_EQ(RunGet(f, kScope), 4);

  SetGlobalVpiContext(nullptr);
}

TEST(CoverageApiOverview, TheLanguagesControlsReachTheVpiSide) {
  SimFixture f;
  VpiContext vpi_ctx;
  vpi_ctx.Attach(f.ctx);
  SetGlobalVpiContext(&vpi_ctx);

  f.ctx.GetCoverageControlState().SetAvailability(std::string(kScope), kToggle,
                                                  CoverageAvailability::kFull);
  ASSERT_EQ(RunControl(f, 0, kScope), static_cast<int>(CoverageStatus::kOk));
  ASSERT_TRUE(vpi_ctx.GetCoverageControlState().IsCollecting(
      std::string(kScope), kToggle));

  ASSERT_EQ(RunControl(f, 1, kScope), static_cast<int>(CoverageStatus::kOk));
  EXPECT_FALSE(vpi_ctx.GetCoverageControlState().IsCollecting(
      std::string(kScope), kToggle));

  SetGlobalVpiContext(nullptr);
}

}  // namespace
