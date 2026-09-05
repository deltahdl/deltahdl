#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = $notasystemtask(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$notasystemtask is not a system task or system "
                            "function this tool implements",
                            3, "20.1"));
}

// The control on the case above. $random is one of the three §20.14 functions
// EvalPrngCall does match, and it reaches that function by the same route an
// unknown name does -- it is the last matcher of the chain, so everything the
// sets ahead of it decline arrives there. A report written at the end of the
// chain rather than after its own matches would name $random too, and this is
// the case that would fail if it did.
TEST(UnknownSystemTask, CallToARecognisedNameIsNotReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = $random;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
