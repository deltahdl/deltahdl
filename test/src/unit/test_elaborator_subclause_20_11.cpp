#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssertControlElab, ControlCallsInEveryForm) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertoff;\n"
      "    $assertoff(0);\n"
      "    $assertoff(1, a1);\n"
      "    $assertpasson;\n"
      "    $assertpassoff(0);\n"
      "    $assertfailoff(0, a1);\n"
      "    $assertcontrol(3);\n"
      "    $assertcontrol(4, , 2);\n"
      "    $assertcontrol(4,,,,t);\n"
      "    $assertcontrol(4, 15, 7, 0, t, a1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(AssertControlElab, DISABLED_AnAssertControlWithoutArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$assertcontrol requires a control_type argument",
                            5, "20.11"));
}

TEST(AssertControlElab,
     DISABLED_AnAssertControlWithEmptyParenthesesIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$assertcontrol requires a control_type argument",
                            5, "20.11"));
}

TEST(AssertControlElab, DISABLED_AStatusTaskWithEmptyParenthesesIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertoff();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$assertoff requires a levels argument inside its parentheses", 5,
      "20.11"));
}

TEST(AssertControlElab, DISABLED_AnActionTaskWithEmptyParenthesesIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertpasson();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$assertpasson requires a levels argument inside its parentheses", 5,
      "20.11"));
}

TEST(AssertControlElab,
     DISABLED_AListEntryThatIsNotAHierarchicalIdentifierIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertoff(0, 1+2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "each scope or assertion argument of $assertoff "
                            "must be a hierarchical identifier",
                            5, "20.11"));
}

TEST(AssertControlElab, DISABLED_ARealControlTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol(4.0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "control_type argument of $assertcontrol must be an integer expression",
      5, "20.11"));
}

TEST(AssertControlElab, DISABLED_AStringControlTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol(\"x\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "control_type argument of $assertcontrol must be an integer expression",
      5, "20.11"));
}

TEST(AssertControlElab, DISABLED_AControlTypeBelowTheTableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "control_type argument of $assertcontrol must be from 1 to 11", 5,
      "20.11"));
}

TEST(AssertControlElab, DISABLED_AControlTypeAboveTheTableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol(12);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "control_type argument of $assertcontrol must be from 1 to 11", 5,
      "20.11"));
}

TEST(AssertControlElab, DISABLED_ARealAssertionTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol(4, 2.0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assertion_type argument of $assertcontrol must be an integer expression",
      5, "20.11"));
}

TEST(AssertControlElab, DISABLED_AStringAssertionTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol(4, \"x\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assertion_type argument of $assertcontrol must be an integer expression",
      5, "20.11"));
}

TEST(AssertControlElab, DISABLED_ARealDirectiveTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol(4, 255, 1.0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "directive_type argument of $assertcontrol must be an integer expression",
      5, "20.11"));
}

TEST(AssertControlElab, DISABLED_AStringDirectiveTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol(4, 255, \"x\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "directive_type argument of $assertcontrol must be an integer expression",
      5, "20.11"));
}

TEST(AssertControlElab, DISABLED_ARealLevelsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertoff(1.0, a1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "levels argument of $assertoff must be an integer expression", 5,
      "20.11"));
}

TEST(AssertControlElab, DISABLED_AStringLevelsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $assertcontrol(4, 255, 7, \"x\", a1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "levels argument of $assertcontrol must be an integer expression", 5,
      "20.11"));
}

TEST(AssertControlElab, ControlCallsInEveryPlace) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  initial $assertoff;\n"
      "endinterface\n"
      "program P;\n"
      "  initial $assertpasson(0);\n"
      "endprogram\n"
      "checker C;\n"
      "  final $assertcontrol(3);\n"
      "endchecker\n"
      "class K;\n"
      "  function void m();\n"
      "    $assertfailoff;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  task tk();\n"
      "    $assertkill;\n"
      "  endtask\n"
      "  function void fn();\n"
      "    $asserton(0);\n"
      "  endfunction\n"
      "  I i();\n"
      "  P p();\n"
      "  C c();\n"
      "  initial begin\n"
      "    tk();\n"
      "    fn();\n"
      "  end\n"
      "  final $assertcontrol(4);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
