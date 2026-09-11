#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

using namespace delta;

namespace {

// §40.2 "Overview" says what the clause is for in one sentence: "This clause
// defines the coverage API in SystemVerilog." One API, and a SystemVerilog one:
// the access functions §40.3.2 gives a design are how coverage is controlled
// and read, and §40.5's VPI routines are named extensions of that API rather
// than a second one of their own - §40.5.3 has them "carry the semantics of
// $coverage_control()". So the coverage a PLI application starts is the
// coverage the design's own $coverage_get reports, and these tests drive one
// side and read the other.

constexpr std::string_view kScope = "top.dut";
constexpr int kToggle = 23;  // §40.3.1 SV_COV_TOGGLE
constexpr int kHier = 11;    // §40.3.1 SV_COV_HIER

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

// §40.2: the API is defined in SystemVerilog, so a design controls and reads
// its own coverage through the language and needs no PLI application to do it.
TEST(CoverageApiOverview, TheLanguageDrivesCoverageOnItsOwn) {
  SimFixture f;
  f.ctx.GetCoverageControlState().SetAvailability(std::string(kScope),
                                                  CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, 0 /* `SV_COV_START */, kScope),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_TRUE(
      f.ctx.GetCoverageControlState().IsCollecting(std::string(kScope)));

  f.ctx.GetCoverageControlState().SetCoveredItems(std::string(kScope), kToggle,
                                                  7);
  EXPECT_EQ(RunGet(f, kScope), 7);
}

// §40.2: the VPI routines are an extension of that one API, so a PLI
// application loaded into a run starts the run's own coverage - the collection
// the design's own access functions are looking at - rather than a collection
// of its own that nothing in the design can see.
TEST(CoverageApiOverview, TheVpiExtensionStartsTheRunsOwnCoverage) {
  SimFixture f;
  VpiContext vpi_ctx;
  vpi_ctx.Attach(f.ctx);
  SetGlobalVpiContext(&vpi_ctx);

  f.ctx.GetCoverageControlState().SetAvailability(std::string(kScope),
                                                  CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx.CreateModule("dut", std::string(kScope));

  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiToggleCoverage, dut),
            static_cast<int>(CoverageStatus::kOk));

  // The design sees what the application started: its own state is collecting,
  // and the count it reads back is the one collection accumulated.
  EXPECT_TRUE(
      f.ctx.GetCoverageControlState().IsCollecting(std::string(kScope)));
  f.ctx.GetCoverageControlState().SetCoveredItems(std::string(kScope), kToggle,
                                                  4);
  EXPECT_EQ(RunGet(f, kScope), 4);

  SetGlobalVpiContext(nullptr);
}

// §40.2, the same one API read from the other side: what the design stops
// through the language is stopped for the application too, so a control issued
// in SystemVerilog is not something a PLI application has to be told about
// separately.
TEST(CoverageApiOverview, TheLanguagesControlsReachTheVpiSide) {
  SimFixture f;
  VpiContext vpi_ctx;
  vpi_ctx.Attach(f.ctx);
  SetGlobalVpiContext(&vpi_ctx);

  f.ctx.GetCoverageControlState().SetAvailability(std::string(kScope),
                                                  CoverageAvailability::kFull);
  ASSERT_EQ(RunControl(f, 0 /* `SV_COV_START */, kScope),
            static_cast<int>(CoverageStatus::kOk));
  ASSERT_TRUE(
      vpi_ctx.GetCoverageControlState().IsCollecting(std::string(kScope)));

  ASSERT_EQ(RunControl(f, 1 /* `SV_COV_STOP */, kScope),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_FALSE(
      vpi_ctx.GetCoverageControlState().IsCollecting(std::string(kScope)));

  SetGlobalVpiContext(nullptr);
}

}  // namespace
