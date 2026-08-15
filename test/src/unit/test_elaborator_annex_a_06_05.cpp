#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimingControlElaboration, DelayInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    #10 x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingControlElaboration, DelayInAlwaysElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  always begin\n"
      "    #5 clk = ~clk;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingControlElaboration, DelayInAlwaysCombError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x, a;\n"
      "  always_comb begin\n"
      "    #10 x = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  // §9.2.2.2.2 is reported at the always_comb keyword, not at the delay.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(TimingControlElaboration, DelayInAlwaysLatchError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x, en, d;\n"
      "  always_latch begin\n"
      "    #5 if (en) x = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not contain timing controls", 3,
                            "9.2.2.3"));
}

TEST(TimingControlElaboration, DelayInFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    #10 ;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
}

TEST(TimingControlElaboration, EventControlStarInAlwaysElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always @(*) y = a & b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingControlElaboration, EventControlInAlwaysCombError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  always_comb begin\n"
      "    @(posedge clk) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  // The event control is a statement inside the block, not the block's own
  // sensitivity list, so §9.2.2.2.2 reports it as a timing control.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(TimingControlElaboration, EventControlInAlwaysLatchError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, en, d, x;\n"
      "  always_latch begin\n"
      "    @(posedge clk) if (en) x = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not contain timing controls", 3,
                            "9.2.2.3"));
}

TEST(TimingControlElaboration, EventControlInFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    @(posedge clk) ;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
}

TEST(TimingControlElaboration, WaitInAlwaysCombError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic done, x;\n"
      "  always_comb begin\n"
      "    wait(done) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(TimingControlElaboration, WaitInFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    wait(1) ;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
}

TEST(TimingControlElaboration, WaitForkInAlwaysCombError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  always_comb begin\n"
      "    wait fork;\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(TimingControlElaboration, WaitForkInFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    wait fork;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
}

TEST(TimingControlElaboration, WaitOrderInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingControlElaboration, WaitOrderInFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    wait_order(a, b) ;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
}

TEST(TimingControlElaboration, ReturnWithValueInVoidFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 3, "13.4.1"));
}

TEST(TimingControlElaboration, ReturnVoidInVoidFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingControlElaboration, ReturnWithValueInIntFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingControlElaboration, CycleDelayInFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    ##5 ;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
}

TEST(TimingControlElaboration, DelayNestedInIfAlwaysCombError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x, a;\n"
      "  always_comb begin\n"
      "    if (a)\n"
      "      #10 x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(TimingControlElaboration, DelayNestedInForLoopAlwaysCombError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  always_comb begin\n"
      "    for (int i = 0; i < 5; i++)\n"
      "      #1 x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(TimingControlElaboration, EventControlNestedInForeverFuncError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    forever @(posedge clk) ;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  // The report stands on the event control nested in the forever, which shares
  // line 3 with the forever itself.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
}

}  // namespace
