#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- delay_control elaboration ---

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// --- event_control elaboration ---

TEST(TimingControlElaboration, EventControlInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  initial begin\n"
      "    @(posedge clk) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// --- wait_statement elaboration ---

TEST(TimingControlElaboration, WaitInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic done, x;\n"
      "  initial begin\n"
      "    wait(done) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

TEST(TimingControlElaboration, WaitForkInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 ;\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// --- jump_statement elaboration ---

TEST(TimingControlElaboration, ReturnWithValueInVoidFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
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

// --- cycle_delay elaboration ---

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
  EXPECT_TRUE(f.has_errors);
}

// --- Timing controls nested in control flow still detected ---

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// --- delay_or_event_control (intra-assignment) elaboration ---

TEST(TimingControlElaboration, IntraAssignDelayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    a = #5 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingControlElaboration, IntraAssignEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial begin\n"
      "    a <= @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingControlElaboration, IntraAssignRepeatEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial begin\n"
      "    a <= repeat(3) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
