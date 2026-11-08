#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/awaiters.h"
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
  EXPECT_EQ(y->value.ToUint64(), 13u);
}

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

TEST(AlwaysCombSensitivitySim, BlockLocalInitializerReadRetriggersProcess) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a = 8'd10;\n"
      "  logic [7:0] b = 8'd3;\n"
      "  logic [7:0] y;\n"
      "  always_comb begin\n"
      "    automatic logic [7:0] tmp = a + b;\n"
      "    y = tmp;\n"
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

TEST(AlwaysCombSensitivitySim, RandcaseWeightReadRetriggersProcess) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] w = 8'd8;\n"
      "  logic [7:0] y;\n"
      "  always_comb begin\n"
      "    randcase\n"
      "      w : y = 8'd21;\n"
      "      (8'd8 - w) : y = 8'd35;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    #1 w = 8'd0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 35u);
}

TEST(AlwaysCombSensitivitySim, InitializerFunctionCallReadRetriggersProcess) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a = 8'd12;\n"
      "  logic [7:0] y;\n"
      "  function automatic logic [7:0] plus_a(input logic [7:0] x);\n"
      "    return x + a;\n"
      "  endfunction\n"
      "  always_comb begin\n"
      "    automatic logic [7:0] tmp = plus_a(8'd5);\n"
      "    y = tmp;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 8'd36;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 41u);
}

bool RunTwoSignalDesign(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    b = 4'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  if (design == nullptr) return false;
  LowerAndRun(design, f);
  return true;
}

TEST(ImplicitSensitivityWatchList, DropsANameThatDesignatesNoObject) {
  SimFixture f;
  ASSERT_TRUE(RunTwoSignalDesign(f));
  std::vector<std::string_view> names{"a", "b[3]", "no_such_signal"};
  DropUnwatchableNames(f.ctx, names);
  EXPECT_EQ(names, std::vector<std::string_view>{"a"});
}

TEST(ImplicitSensitivityWatchList, KeepsEveryNameThatDesignatesAnObject) {
  SimFixture f;
  ASSERT_TRUE(RunTwoSignalDesign(f));
  std::vector<std::string_view> names{"a", "b"};
  DropUnwatchableNames(f.ctx, names);
  EXPECT_EQ(names, (std::vector<std::string_view>{"a", "b"}));
}

TEST(ImplicitSensitivityWatchList, EmptiesAListWhoseNamesAllDesignateNoObject) {
  SimFixture f;
  ASSERT_TRUE(RunTwoSignalDesign(f));
  std::vector<std::string_view> names{"b[3]", "no_such_signal"};
  DropUnwatchableNames(f.ctx, names);
  EXPECT_TRUE(names.empty());
}

TEST(AlwaysCombSensitivitySim, ReactsToAWriteOfTheArrayElementItReads) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  reg [7:0] b;\n"
      "  always_comb b = mem[2];\n"
      "  initial begin\n"
      "    #1 mem[2] = 8'hEF;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xEFu);
}

TEST(AlwaysCombSensitivitySim, StillReactsToAWriteOfThePackedBitItReads) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  reg [7:0] a;\n"
      "  reg b;\n"
      "  always_comb b = a[1];\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    #1 a[1] = 1'b1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AlwaysCombSensitivitySim,
     FormalNamedAsAModuleVariableDoesNotSilenceTheBlocksRead) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int k, y;\n"
      "  function int twice(input int k);\n"
      "    return 2 * k;\n"
      "  endfunction\n"
      "  always_comb y = twice(3) + k;\n"
      "  initial begin\n"
      "    k = 3;\n"
      "    #1 k = 7;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(AlwaysCombSensitivitySim, WriteThroughAClassHandleDoesNotRetrigger) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C; int a = 7; endclass\n"
                       "module t;\n"
                       "  C h = new;\n"
                       "  int x = 1, y;\n"
                       "  always_comb y = x + h.a;\n"
                       "  initial begin\n"
                       "    #5 x = 2;\n"
                       "    #5 h.a = 20;\n"
                       "    #2 $display(\"y@12=%0d\", y);\n"
                       "    #3 x = 3;\n"
                       "    #5 $display(\"y@20=%0d\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "y@12=9\n"
            "y@20=23\n");
}

TEST(AlwaysCombSensitivitySim, VariableIndexReadWakesOnAnElementWrite) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a[3]; int n = 0; int j = 1;\n"
                       "  always_comb n = a[j] + 5;\n"
                       "  initial begin\n"
                       "    #1 a[1] = 1;\n"
                       "    #1 $display(\"n=%0d\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=6\n");
}

TEST(AlwaysCombSensitivitySim, LoopOverAnArrayWakesOnAPatternWrite) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a[3], not_a[3];\n"
                       "  always_comb\n"
                       "    for (int j = 0; j < 3; j++) not_a[j] = !a[j];\n"
                       "  initial begin\n"
                       "    #1 a = '{1, 0, 1};\n"
                       "    #1 $display(\"%0d %0d %0d\", not_a[0], not_a[1],"
                       " not_a[2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 1 0\n");
}

TEST(AlwaysCombSensitivitySim, TwoDimensionalVariableIndexReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a[2][3]; int n = 0; int i = 1, j = 2;\n"
                       "  always_comb n = a[i][j] + 5;\n"
                       "  initial begin\n"
                       "    #1 a[1][2] = 1;\n"
                       "    #1 $display(\"n=%0d\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=6\n");
}

TEST(AlwaysCombSensitivitySim, PackageScopedFunctionReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  int g;\n"
                       "  function int f(int x); return x + g; endfunction\n"
                       "endpackage\n"
                       "module t;\n"
                       "  int a, y;\n"
                       "  always_comb y = p::f(a);\n"
                       "  initial begin\n"
                       "    #1 p::g = 5;\n"
                       "    #1 $display(\"y=%0d\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "y=5\n");
}

TEST(AlwaysCombSensitivitySim, ImportedPackageFunctionReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  int g;\n"
                       "  function int f(int x); return x + g; endfunction\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import p::f;\n"
                       "  int a, y;\n"
                       "  always_comb y = f(a);\n"
                       "  initial begin\n"
                       "    #1 p::g = 5;\n"
                       "    #1 $display(\"y=%0d\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "y=5\n");
}

TEST(AlwaysCombSensitivitySim, PackageScopedReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  int g;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  int y;\n"
                       "  always_comb y = p::g + 1;\n"
                       "  initial begin\n"
                       "    #1 p::g = 5;\n"
                       "    #1 $display(\"y=%0d\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "y=6\n");
}

TEST(AlwaysCombSensitivitySim, ClassStaticMethodReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    static int g;\n"
                       "    static function int f(int x);\n"
                       "      return x + g;\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  int a, y;\n"
                       "  always_comb y = C::f(a);\n"
                       "  initial begin\n"
                       "    #1 C::g = 5;\n"
                       "    #1 $display(\"y=%0d\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "y=5\n");
}

TEST(AlwaysCombSensitivitySim, InstanceFunctionReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  int g;\n"
                       "  function int f(int x); return x + g; endfunction\n"
                       "endmodule\n"
                       "module t;\n"
                       "  sub s();\n"
                       "  int a, y;\n"
                       "  always_comb y = s.f(a);\n"
                       "  initial begin\n"
                       "    #1 s.g = 5;\n"
                       "    #1 $display(\"y=%0d\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "y=5\n");
}

TEST(AlwaysCombSensitivitySim, PackageFunctionsBareCallReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  int g;\n"
                       "  function int h(int x); return x + g; endfunction\n"
                       "  function int f(int x); return h(x); endfunction\n"
                       "endpackage\n"
                       "module t;\n"
                       "  int a, y;\n"
                       "  always_comb y = p::f(a);\n"
                       "  initial begin\n"
                       "    #1 p::g = 5;\n"
                       "    #1 $display(\"y=%0d\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "y=5\n");
}

}  // namespace
