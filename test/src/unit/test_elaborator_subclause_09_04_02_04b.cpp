#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SequenceEventStatementLinks, AutomaticArgInAForkArmErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    fork\n"
      "      @(s(a, b)) $display(\"matched\");\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            9, "9.4.2.4"));
}

TEST(SequenceEventStatementLinks, AutomaticArgInAnAssertionPassActionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    assert (1'b1) @(s(a, b)) $display(\"matched\");\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            8, "9.4.2.4"));
}

TEST(SequenceEventStatementLinks, AutomaticArgInAnAssertionFailActionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    assert (1'b1) else @(s(a, b)) $display(\"matched\");\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            8, "9.4.2.4"));
}

TEST(SequenceEventStatementLinks, AutomaticArgInARandcaseArmErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    randcase\n"
      "      1 : @(s(a, b)) $display(\"matched\");\n"
      "    endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            9, "9.4.2.4"));
}

TEST(SequenceEventStatementLinks, AutomaticArgInARandsequenceCodeBlockErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    randsequence(main)\n"
      "      main : { @(s(a, b)) $display(\"matched\"); };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            9, "9.4.2.4"));
}

}  // namespace
