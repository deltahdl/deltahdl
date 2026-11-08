#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
