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

// §40.2.1 "SystemVerilog coverage API" lists the criteria the API is written
// to: (a) it "shall be similar for all coverages", a common interface across
// the coverage types; (b) "at a minimum" statement, toggle, FSM and assertion
// coverage "shall be supported"; (c) it "shall be extensible in a transparent
// manner, i.e., adding a new coverage type shall not break any existing
// coverage usage"; and (d) it "shall provide means to obtain coverage
// information from specific subhierarchies of the design without requiring the
// user to enumerate all instances in those hierarchies". These tests hold the
// four to the access functions of §40.3.2 and the routines of §40.5.3, which
// are what the API is made of.

constexpr int kAssertion = 20;  // §40.3.1 SV_COV_ASSERTION
constexpr int kFsmState = 21;   // §40.3.1 SV_COV_FSM_STATE
constexpr int kStatement = 22;  // §40.3.1 SV_COV_STATEMENT
constexpr int kToggle = 23;     // §40.3.1 SV_COV_TOGGLE
constexpr int kHier = 11;       // §40.3.1 SV_COV_HIER
constexpr int kStart = 0;       // §40.3.1 SV_COV_START

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

// Criterion (a): the interface is the same whichever coverage is meant - the
// coverage type is an argument of the one call rather than a call of its own,
// so a program written against one type reads another by changing that
// argument and nothing else.
TEST(CoverageApiCriteria, OneInterfaceServesEveryCoverageType) {
  SimFixture f;
  CoverageControlState& cov = f.ctx.GetCoverageControlState();
  cov.SetAvailability(std::string(kScope), CoverageAvailability::kFull);
  cov.SetCoverableItems(std::string(kScope), kStatement, 40);
  cov.SetCoveredItems(std::string(kScope), kStatement, 10);
  cov.SetCoverableItems(std::string(kScope), kToggle, 8);
  cov.SetCoveredItems(std::string(kScope), kToggle, 2);

  // The same three functions, the same argument positions, two coverages.
  EXPECT_EQ(RunControl(f, kStart, kStatement, kScope),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_EQ(RunControl(f, kStart, kToggle, kScope),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_EQ(RunGetMax(f, kStatement, kScope), 40);
  EXPECT_EQ(RunGetMax(f, kToggle, kScope), 8);
  EXPECT_EQ(RunGet(f, kStatement, kScope), 10);
  EXPECT_EQ(RunGet(f, kToggle, kScope), 2);
}

// Criterion (b): the four coverage types §40.3.1 names - assertion, FSM state,
// statement and toggle - are each supported, each with a count of its own, so
// asking for one never answers out of another's tally. (FSM transitions, the
// other half of the FSM coverage the criterion names, are a coverage type the
// standard's own enumerations do not name; criterion (c) is what admits them.)
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

// Criterion (b) on the VPI side of the same API: §40.5.1's four coverage-type
// constants are the same four types, and each controls the collection through
// the routine of §40.5.3.
TEST(CoverageApiCriteria, TheVpiSideNamesTheSameMinimumTypes) {
  SimFixture f;
  VpiContext vpi_ctx;
  vpi_ctx.Attach(f.ctx);
  SetGlobalVpiContext(&vpi_ctx);
  f.ctx.GetCoverageControlState().SetAvailability(std::string(kScope),
                                                  CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx.CreateModule("dut", std::string(kScope));

  for (int coverage_type : {vpiAssertCoverage, vpiFsmStateCoverage,
                            vpiStatementCoverage, vpiToggleCoverage}) {
    EXPECT_EQ(vpi_control(vpiCoverageStart, coverage_type, dut),
              static_cast<int>(CoverageStatus::kOk))
        << "coverage type " << coverage_type;
  }

  SetGlobalVpiContext(nullptr);
}

// Criterion (c): a coverage type this tool has no notion of - a vendor's own,
// say - goes through the same interface and reports that it offers no coverage,
// and asking for it leaves every other type answering exactly as it did. That
// is what "adding a new coverage type shall not break any existing coverage
// usage" asks of the interface.
TEST(CoverageApiCriteria, AnUnknownCoverageTypeBreaksNoExistingUsage) {
  SimFixture f;
  CoverageControlState& cov = f.ctx.GetCoverageControlState();
  cov.SetAvailability(std::string(kScope), CoverageAvailability::kFull);
  cov.SetCoveredItems(std::string(kScope), kToggle, 5);
  constexpr int kVendorCoverageType = 99;

  ASSERT_EQ(RunGet(f, kToggle, kScope), 5);
  EXPECT_EQ(RunGet(f, kVendorCoverageType, kScope),
            static_cast<int>(CoverageStatus::kNoCoverage));
  EXPECT_EQ(RunControl(f, kStart, kVendorCoverageType, kScope),
            static_cast<int>(CoverageStatus::kOk));

  // The type that was there before is unchanged by the one that was not.
  EXPECT_EQ(RunGet(f, kToggle, kScope), 5);
}

// Criterion (d): coverage of a subhierarchy is obtained by naming that
// subhierarchy, in one call. The instances inside it are never named by the
// caller, and a second subhierarchy answers with its own numbers rather than
// with the design's.
TEST(CoverageApiCriteria, ASubhierarchyIsNamedRatherThanEnumerated) {
  SimFixture f;
  CoverageControlState& cov = f.ctx.GetCoverageControlState();
  cov.SetCoveredItems("top.dut", kStatement, 30);
  cov.SetCoveredItems("top.checker", kStatement, 4);

  EXPECT_EQ(RunGet(f, kStatement, "top.dut"), 30);
  EXPECT_EQ(RunGet(f, kStatement, "top.checker"), 4);

  // A subhierarchy the design does not hold is a bad argument, which is how the
  // one call reports that it named nothing rather than silently answering out
  // of the whole design.
  EXPECT_EQ(RunGet(f, kStatement, "top.absent"),
            static_cast<int>(CoverageStatus::kError));
}

}  // namespace
