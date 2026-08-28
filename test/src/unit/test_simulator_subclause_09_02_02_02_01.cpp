#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysCombSensitivitySim, ReactsToDelayedInputChange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #5 a = 8'd7;\n"
      "  end\n"
      "  always_comb result = a * 8'd2;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 14u);
}

TEST(AlwaysCombSensitivitySim, SensitivityTriggersOnAllInputs) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a + b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    #1 b = 8'd10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 11u);
}

TEST(AlwaysCombSensitivitySim, TernaryAllInputsSensitive) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = sel ? a : b;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    #1 sel = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 10u);
}

TEST(AlwaysCombSensitivitySim, ReEvaluatesOnMuxSelectChange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    sel = 8'd0;\n"
      "    #5 sel = 8'd1;\n"
      "  end\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      result = b;\n"
      "    else\n"
      "      result = a;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(AlwaysCombSensitivitySim, FunctionCallArgTriggers) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function automatic logic [7:0] add_one(input logic [7:0] x);\n"
      "    return x + 8'd1;\n"
      "  endfunction\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd9;\n"
      "  always_comb begin\n"
      "    result = add_one(a);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(AlwaysCombSensitivitySim, ConcatenationOperandsTrigger) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] y;\n"
      "  always_comb y = {hi, lo};\n"
      "  initial begin\n"
      "    hi = 4'hA;\n"
      "    lo = 4'h5;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xA5u);
}

TEST(AlwaysCombSensitivitySim, RetriggersOnInputChange) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] a, y;\n"
      "  always_comb y = a + 1;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 11u);
}

TEST(AlwaysCombSensitivitySim, ProcessRegisteredForInputSignal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  const auto& procs = f.ctx.GetSensitiveProcesses("a");
  EXPECT_FALSE(procs.empty());
}

TEST(AlwaysCombSensitivitySim, CaseSelectorChangeSwitchesBranch) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'd0: y = a;\n"
      "      default: y = b;\n"
      "    endcase\n"
      "  initial begin\n"
      "    sel = 2'd0;\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    #1 sel = 2'd1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 20u);
}

TEST(AlwaysCombSensitivitySim, FunctionCallBodyReadRetriggers) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] ext, a, result;\n"
      "  function automatic logic [7:0] add_ext(input logic [7:0] x);\n"
      "    return x + ext;\n"
      "  endfunction\n"
      "  always_comb result = add_ext(a);\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    ext = 8'd10;\n"
      "    #1 ext = 8'd20;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 25u);
}

// §11.5.3 dependency end-to-end: an indexed part-select `a[i +: 4]` reads both
// the array base and the offset `i`. Changing only `i` must retrigger the block
// (the offset is in the runtime sensitivity), so the selected slice updates.
TEST(AlwaysCombSensitivitySim, IndexedPartSelectOffsetRetriggers) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] i;\n"
      "  logic [3:0] y;\n"
      "  always_comb y = a[i +: 4];\n"
      "  initial begin\n"
      "    a = 8'b1011_0100;\n"
      "    i = 2'd0;\n"
      "    #1 i = 2'd2;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  // a[5:2] of 1011_0100 is 1101 == 13.
  EXPECT_EQ(y->value.ToUint64(), 13u);
}

// §8.23 dependency end-to-end: a static method called through the class scope
// resolution operator picks up its argument as a sensitivity contributor, so a
// change to that argument retriggers the block and the result propagates.
TEST(AlwaysCombSensitivitySim, ClassStaticMethodCallArgRetriggers) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int add1(input int x);\n"
      "      add1 = x + 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int a, y;\n"
      "  always_comb y = C#(8)::add1(a);\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    #1 a = 9;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 10u);
}

// §11.5.3 dependency end-to-end: a packed-struct member read `p.lo` puts the
// struct variable in the runtime sensitivity, so changing the struct retriggers
// the block and the member value propagates.
TEST(AlwaysCombSensitivitySim, StructMemberChangeRetriggers) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] hi;\n"
      "    logic [7:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] r;\n"
      "  always_comb r = p.lo;\n"
      "  initial begin\n"
      "    p = 16'hAABB;\n"
      "    #1 p = 16'hCCDD;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0xDDu);
}

TEST(AlwaysCombSensitivitySim, TaskCallInAlwaysCombExecutes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  task automatic compute(input logic [7:0] x, output logic [7:0] r);\n"
      "    r = x + 8'd1;\n"
      "  endtask\n"
      "  always_comb compute(a, result);\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

// §9.2.2.2.1 (printed page 223) settles what an immediate assertion inside an
// always_comb contributes: "An expression used in an immediate assertion (see
// 16.3) within the procedure, or in any function called within the procedure,
// contributes to the implicit sensitivity list of an always_comb as if that
// expression were used as a condition of an if statement. Expressions used in
// assertion action blocks do not contribute to the implicit sensitivity list of
// an always_comb." Its worked example writes `disable_error` in the else action
// and states the block "shall trigger whenever b, c or e changes", naming the
// action block's identifier in neither list.
//
// So `en`, the assertion expression, is in the list, and `a`, read only in the
// pass statement, is not. `a` moves from 10 to 20 at time 1 while `en` is held,
// and `y` keeps the 13 that the time-zero evaluation left it.
TEST(AlwaysCombSensitivitySim, AssertPassStatementReadStaysOutOfSensitivity) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic en = 1'b1;\n"
      "  logic [7:0] a = 8'd10;\n"
      "  logic [7:0] y;\n"
      "  always_comb begin\n"
      "    assert (en) y = a + 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 8'd20;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 13u);
}

// §9.2.2.2.1 (printed page 223): the fail statement is the other half of the
// action block the clause excludes, and the clause's own example puts its
// excluded identifier there. `en` is the assertion expression and drives the
// block; `b` is read only in the fail statement, so changing `b` at time 1
// leaves `y` at the 13 the time-zero evaluation wrote.
TEST(AlwaysCombSensitivitySim, AssertFailStatementReadStaysOutOfSensitivity) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic en = 1'b0;\n"
      "  logic [7:0] b = 8'd10;\n"
      "  logic [7:0] y;\n"
      "  always_comb begin\n"
      "    assert (en) y = 8'd77; else y = b + 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 b = 8'd20;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 13u);
}

// §9.2.2.2.1: the implicit sensitivity list holds "each net or variable
// identifier or select expression that is read within the block", and its three
// exceptions name a declaration, a write and a timing control expression. None
// of them names a statement position, and the action-block exclusion on printed
// page 223 is about assertion action blocks alone, so a read inside a randcase
// item counts. `a` is read only in the item, moves from 10 to 20 at time 1, and
// the re-evaluated block leaves 23 behind. The single item carries weight 3, so
// §18.16 selects it on every draw whatever the random number is.
TEST(AlwaysCombSensitivitySim, RandcaseItemReadRetriggersProcess) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a = 8'd10;\n"
      "  logic [7:0] y;\n"
      "  always_comb begin\n"
      "    randcase\n"
      "      3 : y = a + 8'd3;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 8'd20;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 23u);
}

// §9.2.2.2.1: a randsequence production's code block is a statement within the
// block, and no exception of the clause and no sentence of printed page 223
// excludes it, so the read of `a` inside it belongs to the implicit sensitivity
// list. `a` moves from 10 to 20 at time 1 and the re-evaluated block leaves 23.
TEST(AlwaysCombSensitivitySim, RandsequenceCodeBlockReadRetriggersProcess) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a = 8'd10;\n"
      "  logic [7:0] y;\n"
      "  always_comb begin\n"
      "    randsequence(main)\n"
      "      main : { y = a + 8'd3; };\n"
      "    endsequence\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 8'd20;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 23u);
}

// §9.2.2.2.1 exception (b) leaves out of the implicit sensitivity list "any
// expression that is also written within the block", and names no statement
// position, so a write standing in an assertion action block is a write within
// the block. `tmp` is read by `y = tmp;` and written by the pass statement, so
// exception (b) removes it and the procedure does not re-trigger on its own
// assignment. The count of evaluations is what distinguishes that from a
// procedure sensitive to `tmp`: such a procedure evaluates once at time zero,
// drives `tmp` from x to 13, wakes on that change and evaluates a second time.
// Both evaluations compute the same 13, so the printed line is the only place
// the extra pass shows.
TEST(AlwaysCombSensitivitySim, ActionBlockWriteKeepsNameOutOfSensitivity) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] a = 8'd10;\n"
      "  logic [7:0] tmp;\n"
      "  logic [7:0] y;\n"
      "  always_comb begin\n"
      "    assert (1'b1) tmp = a + 8'd3;\n"
      "    y = tmp;\n"
      "    $display(\"eval %0d\", y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "eval 13\n");
}

// §9.2.2.2.1 (printed page 223) excludes the expressions used in an assertion
// action block from the implicit sensitivity list, and a call to `plus_a` is
// such an expression. What the function reads therefore reaches the list by no
// route: `a` is read only in `plus_a`, `plus_a` is called only from the pass
// statement, and moving `a` from 10 to 20 at time 1 leaves `y` at 13.
//
// The contrast is with AlwaysCombSensitivitySim.FunctionCallBodyReadRetriggers
// above, where the same function is called from an ordinary statement and the
// same change to `a` does re-evaluate the block.
TEST(AlwaysCombSensitivitySim, ActionBlockFunctionCallStaysOutOfSensitivity) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a = 8'd10;\n"
      "  logic [7:0] y;\n"
      "  function automatic logic [7:0] plus_a(input logic [7:0] x);\n"
      "    return x + a;\n"
      "  endfunction\n"
      "  always_comb begin\n"
      "    assert (1'b1) y = plus_a(8'd3);\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 8'd20;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 13u);
}

}  // namespace
