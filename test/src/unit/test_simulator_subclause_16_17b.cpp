#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A design around `body`, the statements of an initial reached at 20: clk
// rises at 5, 15, 25 and so on, data counts its rising edges so that its
// sampled value at the posedge of 10n - 5 is n - 1, a is 1 across the
// posedge of 25 and 35, b across 35 and 45, and c across 45 and 55; the
// run ends at 210.
std::string Design(const std::string& body) {
  return "module m;\n"
         "  logic clk = 0;\n"
         "  logic a = 0, b = 0, c = 0;\n"
         "  int data = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) data <= data + 1;\n"
         "  task automatic wait_for(integer value, output bit success);\n"
         "    expect (@(posedge clk) ##[1:10] data == value) success = 1;\n"
         "      else success = 0;\n"
         "  endtask\n"
         "  initial begin\n"
         "    bit ok;\n"
         "    #20;\n" +
         body +
         "  end\n"
         "  initial begin\n"
         "    #22 a = 1;\n"
         "    #10 b = 1;\n"
         "    #10 c = 1;\n"
         "    #5 a = 0;\n"
         "    #10 c = 0;\n"
         "  end\n"
         "  initial #210 $finish;\n"
         "endmodule\n";
}

// §16.17: the expect statement blocks the process until its property
// succeeds or fails, the evaluation starting at the next clocking event
// and the statement following it running after the Observed region that
// concluded it: reached at 20, a ##1 b ##1 c is evaluated from 25 and
// matches at 45, where the pass statement and the statement after it
// print, and reached again at 45 it is evaluated from 55, where a is 0,
// so the else clause prints there.
TEST(ExpectStatementRun, BlocksUntilTheSequenceMatchesOrFails) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    expect (@(posedge clk) a ##1 b ##1 c)\n"
                        "      $display(\"matched at %0d\", $time);\n"
                        "      else $display(\"failed at %0d\", $time);\n"
                        "    $display(\"after at %0d\", $time);\n"
                        "    expect (@(posedge clk) a ##1 b ##1 c)\n"
                        "      $display(\"matched at %0d\", $time);\n"
                        "      else $display(\"failed at %0d\", $time);\n"
                        "    $display(\"after at %0d\", $time);\n"),
                 f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "matched at 45\nafter at 45\nfailed at 55\nafter at 55\n"
            "$finish at time 210\n");
}

// §16.17: with no else clause a failure is reported through $error, and
// the process goes on past the statement: a is 0 at the posedge of 55,
// the one following the statement reached at 45, so the failure counts
// once and the statement after runs at 55.
TEST(ExpectStatementRun, AFailureWithoutAnElseClauseReportsAnError) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    expect (@(posedge clk) a ##1 b ##1 c) ;\n"
                        "    expect (@(posedge clk) a);\n"
                        "    $display(\"after at %0d\", $time);\n"),
                 f);
  EXPECT_EQ(out, "after at 55\n$finish at time 210\n");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

// §16.17: the clause's wait_for reads the automatic argument value in its
// property, the expect being a blocking statement of the task: called for
// 9 at 20, its evaluation from 25 reads data as 9 at 95, within the 1 to
// 10 ticks, and success is 1 there; called for 30 at 95, none of the ten
// ticks from 115 to 205 reads 30, and success is 0 at 205.
TEST(ExpectStatementRun, ThePropertyReadsAnAutomaticArgument) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    wait_for(9, ok);\n"
                        "    $display(\"ok=%0d at %0d\", ok, $time);\n"
                        "    wait_for(30, ok);\n"
                        "    $display(\"ok=%0d at %0d\", ok, $time);\n"),
                 f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "ok=1 at 95\nok=0 at 205\n$finish at time 210\n");
}

}  // namespace
