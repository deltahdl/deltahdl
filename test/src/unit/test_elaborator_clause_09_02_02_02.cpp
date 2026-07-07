#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysCombLatchWarning, IncompleteIfWarnsLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysCombLatchWarning, CompleteIfElseNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysCombLatchWarning, CaseWithoutDefaultWarnsLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 0;\n"
      "      2'b01: y = 1;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysCombLatchWarning, CaseWithDefaultNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 0;\n"
      "      2'b01: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysCombMultiDriver, MultiDriverTwoAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always_comb y = a;\n"
      "  always_comb y = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, MultiDriverCombAndContAssignErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  assign y = a;\n"
      "  always_comb y = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, DifferentVarsInSeparateCombOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, x, y;\n"
      "  always_comb x = a;\n"
      "  always_comb y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombElaboration, AlwaysCombElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysComb) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(AlwaysCombBasicSim, AlwaysCombExplicitZeros) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a | b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AlwaysCombExtendedSim, MultipleAlwaysCombTime0) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  always_comb x = 8'h11;\n"
      "  always_comb y = 8'h22;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0x11u}, {"y", 0x22u}});
}

TEST(AlwaysCombExtendedSim, AlwaysCombMultiBitAdd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b, y;\n"
      "  always_comb y = a + b;\n"
      "  initial begin\n"
      "    a = 16'h1234;\n"
      "    b = 16'h4321;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x5555u);
}

TEST(AlwaysCombStructFieldAccess, AlwaysCombStructFieldAccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] hi;\n"
      "    logic [7:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] result;\n"
      "  initial p = 16'hABCD;\n"
      "  always_comb begin\n"
      "    result = p.lo;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(AlwaysCombAndGate, AlwaysCombAndGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a & b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h3C;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

TEST(AlwaysCombOrGate, AlwaysCombOrGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a | b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

TEST(AlwaysCombXorGate, AlwaysCombXorGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

TEST(AlwaysCombNotGate, AlwaysCombNotGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, y;\n"
      "  always_comb y = ~a;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0x5Au);
}

TEST(AlwaysCombIfElse, AlwaysCombIfElseTrueBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'hBB;\n"
      "    sel = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xAAu);
}

TEST(AlwaysCombCaseDecode, AlwaysCombCaseDecode) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 2'd2;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'd0: result = 8'd10;\n"
      "      2'd1: result = 8'd20;\n"
      "      2'd2: result = 8'd30;\n"
      "      2'd3: result = 8'd40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(AlwaysComb, Mux2to1Elaborates) {
  EXPECT_TRUE(
      ElabOk("module mux2to1 (input wire a, b, sel,\n"
             "                output logic y);\n"
             "  always_comb begin\n"
             "    if (sel) y = a;\n"
             "    else     y = b;\n"
             "  end\n"
             "endmodule: mux2to1\n"));
}

TEST(AlwaysCombMultiDriver, MultiDriverAlwaysCombAndAlwaysFFErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, y;\n"
      "  always_comb y = a;\n"
      "  always_ff @(posedge clk) y <= 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, MultiDriverAlwaysCombAndAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, y;\n"
      "  always_comb y = a;\n"
      "  always_latch if (en) y = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, SameVarWrittenTwiceInSameProcessOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb begin\n"
      "    y = a;\n"
      "    if (sel) y = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, IndependentElementsNoConflict) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_comb arr[0] = 8'd1;\n"
      "  always_comb arr[1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, OverlappingElementsConflict) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_comb arr[0] = 8'd1;\n"
      "  always_comb arr[0] = 8'd2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, FunctionAssignedLhsCountsAsCombDriver) {
  // §9.2.2.2: a variable assigned inside a function called by the procedure is
  // treated as assigned by the always_comb itself, so a second driver of that
  // variable is an error.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y, z;\n"
      "  function automatic logic f();\n"
      "    y = a;\n"
      "    return a;\n"
      "  endfunction\n"
      "  always_comb z = f();\n"
      "  assign y = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, TaskAssignedLhsNotCombDriver) {
  // §9.2.2.2: variables assigned inside a task called by the procedure are
  // explicitly excluded, so the always_comb is not a driver of 'y' and the lone
  // continuous assignment to 'y' is legal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y, z;\n"
      "  task automatic t();\n"
      "    y = a;\n"
      "  endtask\n"
      "  always_comb begin\n"
      "    t();\n"
      "    z = a;\n"
      "  end\n"
      "  assign y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, WholeArrayAndElementConflict) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_comb arr[0] = 8'd1;\n"
      "  always_comb arr = '{8'd3, 8'd4};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, IndependentElementAndContinuousAssignNoConflict) {
  // §9.2.2.2: the single-driver rule permits one element of an array to be
  // driven by an always_comb while a different element is driven continuously,
  // since their longest static prefixes do not overlap.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_comb arr[0] = 8'd1;\n"
      "  assign arr[1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, IndependentStructFieldsNoConflict) {
  // §9.2.2.2: the structure analog of independent elements — distinct fields
  // driven by separate always_comb procedures have non-overlapping prefixes and
  // are therefore not multiple drivers of the same variable.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "  } pair_t;\n"
      "  pair_t s;\n"
      "  always_comb s.a = 8'd1;\n"
      "  always_comb s.b = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, WholeStructAndFieldConflict) {
  // §9.2.2.2: when one always_comb drives a whole structure and another drives
  // a field of it, the prefixes overlap, so it is an illegal multiple driver.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "  } pair_t;\n"
      "  pair_t s;\n"
      "  always_comb s = 16'd0;\n"
      "  always_comb s.a = 8'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombTiming, NonblockingIntraAssignDelayAllowed) {
  // §9.2.2.2 shows `d <= #1ns b & c;` as a legal always_comb body. An
  // intra-assignment delay on a nonblocking assignment is not a statement-level
  // timing control, so it shall not be rejected as one.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic b, c, d;\n"
      "  always_comb d <= #1ns b & c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, MultiDriverCombAndGeneralAlwaysErrors) {
  // §9.2.2.2: an always_comb LHS shall not be assigned by any other process; a
  // general-purpose always block driving the same variable is illegal.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always_comb y = a;\n"
      "  always @(a or b) y = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, MultiDriverCombAndInitialErrors) {
  // §9.2.2.2: an initial block is also a process, so it may not assign a
  // variable that an always_comb drives.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb y = a;\n"
      "  initial y = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, CombAndGeneralAlwaysDifferentVarsOk) {
  // §9.2.2.2: the rule only applies when the same variable is driven; distinct
  // targets in an always_comb and a general always are legal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, x, y;\n"
      "  always_comb x = a;\n"
      "  always @(b) y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, CombAndGeneralAlwaysIndependentElementsOk) {
  // §9.2.2.2 / §11.5.3: one array element driven by always_comb and a different
  // element driven by a general always have non-overlapping longest static
  // prefixes, so they are independent and legal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_comb arr[0] = 8'd1;\n"
      "  always @(posedge clk) arr[1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, IndependentElementsParamIndexNoConflict) {
  // §9.2.2.2 / §11.5.3: the independent-elements exception depends on the
  // longest static prefix, which keeps a select in the prefix only when its
  // index is a constant expression. A module parameter is such a constant
  // (§11.2.1). Two distinct parameter indices name distinct elements, so the
  // two always_comb procedures drive non-overlapping prefixes and are legal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int P0 = 0, parameter int P1 = 1);\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_comb arr[P0] = 8'd1;\n"
      "  always_comb arr[P1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, IndependentElementsLocalparamIndexNoConflict) {
  // §9.2.2.2 / §11.5.3: a localparam is also a constant expression (§11.2.1),
  // so two distinct localparam indices resolve to distinct elements and the
  // two always_comb drivers do not overlap.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int P0 = 0;\n"
      "  localparam int P1 = 1;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_comb arr[P0] = 8'd1;\n"
      "  always_comb arr[P1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, OverlappingElementsParamIndexConflict) {
  // §9.2.2.2 / §11.5.3 (negative form): when both always_comb procedures index
  // the same parameter, the constant folds to the same element, the longest
  // static prefixes overlap, and the multiple-driver rule rejects it.
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter int P = 0);\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_comb arr[P] = 8'd1;\n"
      "  always_comb arr[P] = 8'd2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombLatchWarning, NestedIncompleteIfWarnsLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always_comb\n"
      "    if (a)\n"
      "      if (b) y = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

}  // namespace
