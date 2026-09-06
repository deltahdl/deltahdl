#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborate, lower and run `src`, which is how a $name in a source reaches the
// dispatch chain that classifies it. Returns false when the source did not
// elaborate, which a case reads as having covered nothing.
bool RunSource(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return false;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return true;
}

// A source calling `name` as a statement, which is how §20.11's assertion
// control tasks and §21.7's dump tasks are written. The call stands on line 2.
std::string CallingTask(const std::string& name) {
  return "module t;\n"
         "  initial " +
         name +
         ";\n"
         "endmodule\n";
}

// A source calling `name` for its value, which is how §20.12's sampled value
// functions, §20.13's coverage functions and §20.15's queue functions are
// written. The call stands on line 3.
std::string CallingFunction(const std::string& call) {
  return "module t;\n"
         "  int x;\n"
         "  initial x = " +
         call +
         ";\n"
         "endmodule\n";
}

// The report a name outside §20.1 and Clause 21 is owed.
std::string NotImplemented(const std::string& name) {
  return name + " is not a system task or system function this tool implements";
}

// §20.1 catalogues the system tasks and system functions SystemVerilog has,
// naming each of them under the subclause that defines it, and says that
// "Clause 21 presents additional system tasks and system functions that are
// specific to I/O operations". A `$name` outside those two clauses is a call
// this simulator can carry out no part of.
//
// Every such call evaluated to a one-bit zero and was discarded in silence,
// because EvalPrngCall stood at the end of the dispatch chain and answered
// with a value for the names it did not match rather than saying it did not
// match them. A misspelling, a task the standard defines that deltahdl has not
// implemented, and a name the standard has never had were the same thing to a
// reader of the run: nothing. It is why the $vcdclose defect of #3254 survived
// -- the call looked like it had worked.
TEST(UnknownSystemTask, CallToAnUnknownNameIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$notasystemtask(1)")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotImplemented("$notasystemtask"), 3, "20.1"));
}

// The control on the case above. $random is one of the three §20.14 functions
// EvalPrngCall does match, and it reaches that function by the same route an
// unknown name does -- it is the last matcher of the chain, so everything the
// sets ahead of it decline arrives there. A report written at the end of the
// chain rather than after its own matches would name $random too, and this is
// the case that would fail if it did.
TEST(UnknownSystemTask, CallToARecognisedNameIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$random")));
  EXPECT_FALSE(f.diag.HasErrors());
}

// Reaching the report is what a classifier standing for a set of names has to
// leave possible. IsVcdSysCall claimed every name beginning $dump, so a
// misspelling of a §21.7 dump task was answered by EvalVcdSysCall with a zero
// and never arrived here. §21.7 names fourteen dump tasks and $dumpvasr is not
// one of them.
TEST(UnknownSystemTask, AMisspeltDumpTaskIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingTask("$dumpvasr")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotImplemented("$dumpvasr"),
                            2, "20.1"));
}

// The control: §21.7.1.6 gives $dumpflush, so the fourteen-name list has to
// still admit it. Without this a classifier that claimed nothing would pass
// the case above.
TEST(UnknownSystemTask, ADumpTaskIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingTask("$dumpflush")));
  EXPECT_FALSE(f.diag.HasErrors());
}

// IsVerifSysCall is a separate classifier with sinks of its own, and it
// claimed every name beginning $assert. §20.11's Syntax 20-12 names ten
// assertion control tasks and $assertofff is not one of them.
TEST(UnknownSystemTask, AMisspeltAssertionControlTaskIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingTask("$assertofff")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotImplemented("$assertofff"),
                            2, "20.1"));
}

// The control on the case above: $assertoff is one of the ten.
TEST(UnknownSystemTask, AnAssertionControlTaskIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingTask("$assertoff")));
  EXPECT_FALSE(f.diag.HasErrors());
}

// The _gclk arm was a suffix test rather than a prefix one, anchored to no $ at
// all, so a fix keyed on the two prefixes alone would have left it. §20.12's
// Syntax 20-13 names ten global clocking functions and $risen_gclk is not one
// of them, though it ends the way all ten do. The name has to end in _gclk for
// the case to reach the arm at issue: a misspelling that breaks the suffix,
// such as $rose_gclkk, was never claimed by it and is reported either way.
TEST(UnknownSystemTask, AMisspeltGlobalClockingFunctionIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$risen_gclk(1)")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotImplemented("$risen_gclk"),
                            3, "20.1"));
}

// The control on the case above: $rose_gclk is one of the ten. §16.9.4 lets a
// global clocking sampled value function be used only where a global clocking
// is declared, so the module declares one -- without it the source is rejected
// under §16.9.4 and the case would report a rule it is not about.
TEST(UnknownSystemTask, AGlobalClockingFunctionIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f,
                        "module t;\n"
                        "  int x;\n"
                        "  logic clk;\n"
                        "  global clocking @(posedge clk); endclocking\n"
                        "  initial x = $rose_gclk(clk);\n"
                        "endmodule\n"));
  EXPECT_FALSE(f.diag.HasErrors());
}

// §20.13 names five coverage system functions. The $coverage prefix claimed
// anything under it, and EvalCoverageSysCall answered what its five exact
// matches declined with a 32-bit zero of its own.
TEST(UnknownSystemTask, AMisspeltCoverageFunctionIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$coverage_gett")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotImplemented("$coverage_gett"), 3, "20.1"));
}

// §20.15 names five stochastic analysis tasks and functions. The $q_ prefix
// claimed anything under it, and EvalStochasticQueue answered what its five
// exact matches declined with a 32-bit zero of its own.
TEST(UnknownSystemTask, AMisspeltStochasticQueueFunctionIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$q_ad(1)")));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), NotImplemented("$q_ad"), 3, "20.1"));
}

}  // namespace
