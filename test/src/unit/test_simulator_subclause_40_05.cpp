// Tests for IEEE 1800-2023 §40.5 "VPI coverage extensions".
//
// The clause is a heading over three subclauses and writes no rule of its own,
// which is exactly what it has to say: §40.5.1's enumerations, §40.5.2's
// extension of vpi_get() and §40.5.3's extension of vpi_control() are one
// extension of one API, not three. §40.5.3 says so of every operation it
// defines - the semantics and behavior "are per the $coverage_control() system
// function", "per the equivalent system function $coverage_save()", "per the
// equivalent system function $coverage_merge()" - and §40.5.2 says it of the
// query, the number of covered items of a coverage type in an instance being
// the figure $coverage_get reports for that instance. So a coverage type named
// through VPI and the same type named through §40.3.1's `SV_COV_* macros are
// one type, a database one door writes is one the other door reads, and what
// one door resets is what the other stops reporting.
//
// Each subclause has a file of its own that drives its own door. These cases
// are the crossings, which no one of those files can make: the state is primed
// or read in §40.3.2's terms and reached through §40.5's, or the reverse.

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_coverage_syscall.h"
#include "parser/ast.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §40.3.1 coverage-type constants, the values the `SV_COV_* macros carry. The
// §40.5.1 properties vpiAssertCoverage, vpiStatementCoverage and
// vpiToggleCoverage name the same three types.
constexpr int kSvCovAssertion = 20;
constexpr int kSvCovStatement = 22;
constexpr int kSvCovToggle = 23;

// §40.3.1 `SV_COV_HIER: the named instance and the hierarchy below it.
constexpr int kSvCovHier = 11;

constexpr int kOk = static_cast<int>(CoverageStatus::kOk);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);

// Evaluates $coverage_get(coverage_type, `SV_COV_HIER, "scope") (§40.3.2.3)
// through the production evaluator, which is the language's own door onto the
// figure §40.5.2 has vpi_get() report.
int RunCoverageGet(SimFixture& f, int coverage_type, std::string_view scope) {
  auto* call = MkSysCall(f.arena, "$coverage_get",
                         {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
                          MkInt(f.arena, kSvCovHier), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

// A run with a VPI context attached to it, so the language's coverage
// functions and the VPI routines are working on the one run rather than on two
// states that happen to be spelled alike.
class VpiCoverageExtensions : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.Attach(f_.ctx);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  CoverageControlState& Cov() { return f_.ctx.GetCoverageControlState(); }

  SimFixture f_;
  VpiContext vpi_ctx_;
};

// §40.5.3: vpi_control(vpiCoverageMerge, ...) is specified "per the equivalent
// system function $coverage_merge()", so the database a $coverage_save wrote
// under `SV_COV_ASSERTION is a database it can load. Naming the type
// vpiAssertCoverage instead of `SV_COV_ASSERTION is a difference of spelling
// between two clauses, not of which coverage is meant.
TEST_F(VpiCoverageExtensions, WhatTheSystemFunctionSavedTheVpiMergeLoads) {
  Cov().SetCoverageAvailableForSave(kSvCovAssertion, true);
  ASSERT_EQ(
      RunCoverageSysCall(f_, "$coverage_save", kSvCovAssertion, "run.cov"),
      kOk);

  EXPECT_EQ(vpi_control(vpiCoverageMerge, vpiAssertCoverage, "run.cov"), kOk);
  EXPECT_EQ(Cov().MergeCount("run.cov"), 1u);
}

// And the crossing the other way: a database written through
// vpi_control(vpiCoverageSave, vpiToggleCoverage, ...) is one $coverage_merge
// finds under `SV_COV_TOGGLE. Reported the wrong way round, each door would
// have said `SV_COV_NOCOV - the database was found but holds no coverage of the
// type asked for - over the coverage the other had just written into it.
TEST_F(VpiCoverageExtensions, WhatTheVpiSaveWroteTheSystemFunctionMerges) {
  Cov().SetCoverageAvailableForSave(kSvCovToggle, true);
  ASSERT_EQ(vpi_control(vpiCoverageSave, vpiToggleCoverage, "vpi.cov"), kOk);

  EXPECT_EQ(RunMerge(f_, kSvCovToggle, "vpi.cov"), kOk);
  EXPECT_EQ(Cov().MergeCount("vpi.cov"), 1u);
}

// A type neither door has coverage of is still nothing to save, so the
// agreement is about which type is meant rather than about answering `SV_COV_OK
// to everything: only the toggle type was made available above.
TEST_F(VpiCoverageExtensions, AVpiSaveOfATypeWithNoCoverageStillSavesNothing) {
  Cov().SetCoverageAvailableForSave(kSvCovToggle, true);

  EXPECT_EQ(vpi_control(vpiCoverageSave, vpiStatementCoverage, "vpi.cov"),
            kNoCov);
  EXPECT_EQ(Cov().SaveCount("vpi.cov"), 0u);
}

// §40.5.2: vpi_get(<coverageType>, instance_handle) "returns the number of
// covered items of the given coverage type in the given instance", which is
// what $coverage_get reports for the same instance (§40.3.2.3). Both doors are
// asked over one scope that has covered 7 of its 12 coverable statements, and
// the clause is that they answer alike.
TEST_F(VpiCoverageExtensions, TheVpiQueryReportsTheCoverageTheLanguageReports) {
  Cov().SetCoverableItems("top.dut", kSvCovStatement, 12);
  Cov().SetCoveredItems("top.dut", kSvCovStatement, 7);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");

  EXPECT_EQ(vpi_get(vpiStatementCoverage, dut), 7);
  EXPECT_EQ(vpi_get(vpiStatementCoverage, dut),
            RunCoverageGet(f_, kSvCovStatement, "top.dut"));
}

// The two halves of the extension over one state: §40.5.3's reset "resets all
// available coverage information in the specified hierarchy" (§40.3.2.1), and
// what it resets is what §40.5.2's query was reporting. A query answered out of
// a store of its own would go on reporting the 7 covered statements after the
// control had cleared them, and the language's own function would disagree with
// it.
TEST_F(VpiCoverageExtensions, TheVpiControlResetsWhatTheVpiQueryReports) {
  Cov().SetAvailability("top.dut", CoverageAvailability::kFull);
  Cov().SetCoverableItems("top.dut", kSvCovStatement, 12);
  Cov().SetCoveredItems("top.dut", kSvCovStatement, 7);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");
  ASSERT_EQ(vpi_get(vpiStatementCoverage, dut), 7);

  ASSERT_EQ(vpi_control(vpiCoverageReset, vpiStatementCoverage, dut), kOk);

  EXPECT_EQ(vpi_get(vpiStatementCoverage, dut), kNoCov);
  EXPECT_EQ(RunCoverageGet(f_, kSvCovStatement, "top.dut"), kNoCov);
}

}  // namespace
}  // namespace delta
