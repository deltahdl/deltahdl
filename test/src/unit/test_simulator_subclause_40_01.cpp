#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_preprocessor.h"
#include "fixture_simulator.h"
#include "helpers_fsm_pragma_lexing.h"
#include "parser/ast.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

using namespace delta;

namespace {

// §40.1 "General" says what clause 40 describes, as five items: the
// SystemVerilog coverage API, the coverage constants, the coverage VPI
// routines, FSM recognition, and the coverage VPI extensions. It states no rule
// of its own - each item is written out in a subclause of its own, §40.3.2 for
// the access functions the API is, §40.3.1 for the constants, §40.5.3 for the
// routines, §40.4 for the pragmas, and §40.5.1 for the enumeration extensions -
// so what §40.1 claims is that this clause provides all five. These tests take
// them one at a time and observe this tool answering for each.

constexpr std::string_view kScope = "$root.tb.unit1";
constexpr int kToggle = 23;  // §40.3.1 SV_COV_TOGGLE

// §40.1, first item - the SystemVerilog coverage API. What the clause puts
// behind that name is the built-in coverage access system functions of §40.3.2,
// which a design calls the way it calls any system function: a control starts
// the collection and a query reads back what has been covered.
TEST(CoverageApiGeneral, TheApiIsTheBuiltInAccessFunctions) {
  SimFixture f;
  f.ctx.GetCoverageControlState().SetAvailability(std::string(kScope),
                                                  CoverageAvailability::kFull);

  auto* control = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, 0 /* `SV_COV_START */),
       MkInt(f.arena, static_cast<uint64_t>(kToggle)),
       MkInt(f.arena, 11 /* `SV_COV_HIER */), MkStr(f.arena, kScope)});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(control, f.ctx, f.arena).ToUint64()),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_TRUE(
      f.ctx.GetCoverageControlState().IsCollecting(std::string(kScope)));

  f.ctx.GetCoverageControlState().SetCoveredItems(std::string(kScope), kToggle,
                                                  12);
  auto* get = MkSysCall(
      f.arena, "$coverage_get",
      {MkInt(f.arena, static_cast<uint64_t>(kToggle)),
       MkInt(f.arena, 11 /* `SV_COV_HIER */), MkStr(f.arena, kScope)});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(get, f.ctx, f.arena).ToUint64()), 12);
}

// §40.1, second item - the coverage constants. §40.3.1 has them predefined as
// text macros, so a source file writes the control, the coverage type and the
// scope by name rather than by number, and the numbers the three groups expand
// to are what the access functions above were given.
TEST(CoverageApiGeneral, TheConstantsArePredefinedByName) {
  PreprocFixture f;
  auto out = Preprocess("`SV_COV_START `SV_COV_TOGGLE `SV_COV_HIER\n", f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(out.find('0'), std::string::npos);
  EXPECT_NE(out.find("23"), std::string::npos);
  EXPECT_NE(out.find("11"), std::string::npos);
}

// §40.1, third item - the coverage VPI routines. §40.5.3 extends vpi_control()
// so a PLI application reaches the same collection the system functions do,
// naming the scope by a handle rather than by a string.
TEST(CoverageApiGeneral, TheVpiRoutinesControlTheSameCollection) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);

  vpi_ctx.GetCoverageControlState().SetAvailability(
      "top.dut", CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx.CreateModule("dut", "top.dut");

  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiToggleCoverage, dut),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_TRUE(vpi_ctx.GetCoverageControlState().IsCollecting("top.dut"));

  SetGlobalVpiContext(nullptr);
}

// §40.1, fourth item - FSM recognition. §40.4 has no automatic extraction to
// require; what it defines is the pragma a source writes to force it, and the
// lexer is where that comment stops being a comment.
TEST(CoverageApiGeneral, FsmRecognitionReadsThePragma) {
  auto pragmas = CollectFsmPragmas("/* tool state_vector cur_state */");

  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
}

// §40.1, fifth item - the coverage VPI extensions. §40.5.1 adds the coverage
// types and properties to the VPI enumerations, which is what a routine of the
// third item is given to say which coverage it means; each is defined and each
// is its own value.
TEST(CoverageApiGeneral, TheVpiEnumerationsCarryTheCoverageTypes) {
  EXPECT_NE(vpiAssertCoverage, vpiFsmStateCoverage);
  EXPECT_NE(vpiFsmStateCoverage, vpiStatementCoverage);
  EXPECT_NE(vpiStatementCoverage, vpiToggleCoverage);
  EXPECT_NE(vpiToggleCoverage, vpiAssertCoverage);

  // The per-item properties the same extensions add, which §40.5.2 reads an
  // assertion's own coverage back through.
  EXPECT_NE(vpiCovered, vpiCoveredCount);
  EXPECT_NE(vpiAssertAttemptCovered, vpiAssertSuccessCovered);
  EXPECT_NE(vpiAssertSuccessCovered, vpiAssertFailureCovered);
}

}  // namespace
