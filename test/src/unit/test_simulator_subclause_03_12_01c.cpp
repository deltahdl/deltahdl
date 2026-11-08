#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CompilationUnitSearchOrderSim, ASubroutineLocalIsFoundBeforeTheUnitsName) {
  EXPECT_EQ(RunAndGet("int b = 1;\n"
                      "module top;\n"
                      "  int y, r;\n"
                      "  task t;\n"
                      "    int b;\n"
                      "    b = 2;\n"
                      "    y = b;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    t();\n"
                      "    r = y * 10 + $unit::b;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            21u);
}

TEST(CompilationUnitSearchOrderSim,
     TheUnitsFunctionIsFoundBeforeAnEnclosingInstances) {
  EXPECT_EQ(RunAndGet("function int f();\n"
                      "  return 1;\n"
                      "endfunction\n"
                      "module child;\n"
                      "  int y;\n"
                      "  initial y = f();\n"
                      "endmodule\n"
                      "module top;\n"
                      "  function int f();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "  child c();\n"
                      "endmodule\n",
                      "c.y"),
            1u);
}

TEST(CompilationUnitSearchOrderSim,
     DollarUnitReachesTheUnitsVariablePastATaskLocal) {
  EXPECT_EQ(RunAndGet("bit b = 1;\n"
                      "int r;\n"
                      "task t;\n"
                      "  int b;\n"
                      "  b = 5 + $unit::b;\n"
                      "  r = b;\n"
                      "endtask\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    t();\n"
                      "    y = r;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            6u);
}

TEST(CompilationUnitSearchOrderSim,
     DollarUnitCallsTheUnitsFunctionPastTheModules) {
  EXPECT_EQ(RunAndGet("function int f();\n"
                      "  return 1;\n"
                      "endfunction\n"
                      "module m;\n"
                      "  function int f();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "  int y;\n"
                      "  initial y = $unit::f() * 10 + f();\n"
                      "endmodule\n",
                      "y"),
            12u);
}

TEST(CompilationUnitSearchOrderSim, DollarUnitCallFromAModuleFunctionsBody) {
  EXPECT_EQ(RunAndGet("function int f();\n"
                      "  return 1;\n"
                      "endfunction\n"
                      "module m;\n"
                      "  function int f();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "  function int g();\n"
                      "    return $unit::f() * 10 + f();\n"
                      "  endfunction\n"
                      "  int y;\n"
                      "  initial y = g();\n"
                      "endmodule\n",
                      "y"),
            12u);
}

TEST(CompilationUnitSearchOrderSim, DollarUnitCallFromAGenerateBlock) {
  EXPECT_EQ(RunAndGet("function int f();\n"
                      "  return 1;\n"
                      "endfunction\n"
                      "module m;\n"
                      "  int y;\n"
                      "  if (1) begin : g\n"
                      "    function int f();\n"
                      "      return 2;\n"
                      "    endfunction\n"
                      "    initial y = $unit::f() * 10 + f();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            12u);
}

TEST(CompilationUnitSearchOrderSim,
     DollarUnitEnablesTheUnitsTaskPastTheModules) {
  EXPECT_EQ(RunAndGet("int hits;\n"
                      "task t;\n"
                      "  hits = hits + 1;\n"
                      "endtask\n"
                      "module m;\n"
                      "  int own, y;\n"
                      "  task t;\n"
                      "    own = own + 10;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    $unit::t;\n"
                      "    $unit::t();\n"
                      "    y = hits * 100 + own;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            200u);
}

TEST(CompilationUnitSearchOrderSim,
     ANestedModulesEnclosingVariableIsFoundFirst) {
  EXPECT_EQ(RunAndGet("int x = 1;\n"
                      "module outer;\n"
                      "  int x = 2;\n"
                      "  module inner;\n"
                      "    int y;\n"
                      "    initial y = x;\n"
                      "  endmodule\n"
                      "  inner i();\n"
                      "endmodule\n",
                      "i.y"),
            2u);
}

TEST(CompilationUnitSearchOrderSim,
     ANestedModulesEnclosingParameterIsFoundFirst) {
  EXPECT_EQ(RunAndGet("localparam int K = 1;\n"
                      "module outer;\n"
                      "  localparam int K = 2;\n"
                      "  module inner;\n"
                      "    int y;\n"
                      "    initial y = K;\n"
                      "  endmodule\n"
                      "  inner i();\n"
                      "endmodule\n",
                      "i.y"),
            2u);
}

TEST(CompilationUnitSearchOrderSim,
     ANestedModulesEnclosingFunctionIsFoundFirst) {
  EXPECT_EQ(RunAndGet("function int f();\n"
                      "  return 1;\n"
                      "endfunction\n"
                      "module outer;\n"
                      "  function int f();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "  module inner;\n"
                      "    int y;\n"
                      "    initial y = f();\n"
                      "  endmodule\n"
                      "  inner i();\n"
                      "endmodule\n",
                      "i.y"),
            2u);
}

TEST(CompilationUnitSearchOrderSim, TheSearchClimbsEveryEnclosingDeclaration) {
  EXPECT_EQ(RunAndGet("int x = 10;\n"
                      "function int f();\n"
                      "  return 1;\n"
                      "endfunction\n"
                      "module outer;\n"
                      "  int x = 20;\n"
                      "  function int f();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "  module middle;\n"
                      "    module inner;\n"
                      "      int y;\n"
                      "      initial y = x + f();\n"
                      "    endmodule\n"
                      "    inner i();\n"
                      "  endmodule\n"
                      "  middle m();\n"
                      "endmodule\n",
                      "m.i.y"),
            22u);
}

TEST(CompilationUnitSearchOrderSim, ANestedModulesOwnVariableIsFoundBeforeAll) {
  EXPECT_EQ(RunAndGet("int x = 1;\n"
                      "module outer;\n"
                      "  int x = 2;\n"
                      "  module inner;\n"
                      "    int x = 3;\n"
                      "    int y;\n"
                      "    initial y = x;\n"
                      "  endmodule\n"
                      "  inner i();\n"
                      "endmodule\n",
                      "i.y"),
            3u);
}

TEST(CompilationUnitSearchOrderSim, ANestedModulesOwnFunctionIsFoundBeforeAll) {
  EXPECT_EQ(RunAndGet("function int f();\n"
                      "  return 1;\n"
                      "endfunction\n"
                      "module outer;\n"
                      "  function int f();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "  module inner;\n"
                      "    function int f();\n"
                      "      return 3;\n"
                      "    endfunction\n"
                      "    int y;\n"
                      "    initial y = f();\n"
                      "  endmodule\n"
                      "  inner i();\n"
                      "endmodule\n",
                      "i.y"),
            3u);
}

constexpr const char* kTopsAndHolder =
    "module top;\n"
    "  int x = 7;\n"
    "  wire [7:0] w = 8'd7;\n"
    "  holder h();\n"
    "endmodule\n"
    "module leaf;\n"
    "  int x = 3;\n"
    "  wire [7:0] w = 8'd3;\n"
    "endmodule\n";

uint64_t HolderRuns(const std::string& unit_items, const std::string& decls,
                    const std::string& stmt) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(unit_items + kTopsAndHolder +
                                         "module holder;\n"
                                         "  leaf top();\n"
                                         "  int y;\n" +
                                         decls + "  initial #1 " + stmt +
                                         "\n"
                                         "endmodule\n",
                                     f);
  EXPECT_FALSE(f.has_errors);
  if (design == nullptr) return ~0ull;
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("h.y");
  return y == nullptr ? ~0ull : y->value.ToUint64();
}

TEST(CompilationUnitSearchOrderSim, AUnitFunctionsPathIsReadFromRoot) {
  EXPECT_EQ(HolderRuns("function int f();\n"
                       "  return top.x;\n"
                       "endfunction\n",
                       "", "y = f();"),
            7u);
}

TEST(CompilationUnitSearchOrderSim, AUnitClassMethodsPathIsReadFromRoot) {
  EXPECT_EQ(HolderRuns("class K;\n"
                       "  function int g();\n"
                       "    return top.x;\n"
                       "  endfunction\n"
                       "endclass\n",
                       "  K k = new;\n", "y = k.g();"),
            7u);
}

TEST(CompilationUnitSearchOrderSim, AUnitTasksPathIsReadFromRoot) {
  EXPECT_EQ(HolderRuns("task t(output int v);\n"
                       "  v = top.x;\n"
                       "endtask\n",
                       "", "t(y);"),
            7u);
}

TEST(CompilationUnitSearchOrderSim, AUnitFunctionsPathToANetIsReadFromRoot) {
  EXPECT_EQ(HolderRuns("function int f();\n"
                       "  return top.w;\n"
                       "endfunction\n",
                       "", "y = f();"),
            7u);
}

TEST(CompilationUnitSearchOrderSim, AUnitVariablesMemberIsNoPathFromRoot) {
  EXPECT_EQ(RunAndGet("typedef struct {\n"
                      "  int a;\n"
                      "} st_t;\n"
                      "st_t s = '{a: 4};\n"
                      "function int f();\n"
                      "  return s.a;\n"
                      "endfunction\n"
                      "module top;\n"
                      "  st_t s = '{a: 9};\n"
                      "  int y;\n"
                      "  initial y = f();\n"
                      "endmodule\n",
                      "y"),
            4u);
}

TEST(CompilationUnitSearchOrderSim, AModuleDrivesAndReadsTheUnitsNet) {
  EXPECT_EQ(RunAndGet("wire w;\n"
                      "module top;\n"
                      "  logic y;\n"
                      "  assign w = 1;\n"
                      "  initial #1 y = w;\n"
                      "endmodule\n",
                      "y"),
            1u);
}

TEST(CompilationUnitSearchOrderSim, AnInstanceDrivesTheUnitsNetTheTopReads) {
  EXPECT_EQ(RunAndGet("wire [7:0] w;\n"
                      "module drv;\n"
                      "  assign w = 8'hA5;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  logic [7:0] y;\n"
                      "  drv d();\n"
                      "  initial #1 y = w;\n"
                      "endmodule\n",
                      "y"),
            0xA5u);
}

TEST(CompilationUnitSearchOrderSim, TheUnitsNetResolvesByItsNetType) {
  EXPECT_EQ(RunAndGet("wand w;\n"
                      "module d1;\n"
                      "  assign w = 1'b1;\n"
                      "endmodule\n"
                      "module d0;\n"
                      "  assign w = 1'b0;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  logic y;\n"
                      "  d1 a();\n"
                      "  d0 b();\n"
                      "  initial #1 y = (w === 1'b0);\n"
                      "endmodule\n",
                      "y"),
            1u);
}

TEST(CompilationUnitSearchOrderSim, OneModulesTwoDriversOfTheUnitsWand) {
  EXPECT_EQ(RunAndGet("wand w;\n"
                      "module top;\n"
                      "  logic y;\n"
                      "  assign w = 1'b1;\n"
                      "  assign w = 1'b0;\n"
                      "  initial #1 y = (w === 1'b0);\n"
                      "endmodule\n",
                      "y"),
            1u);
}

TEST(CompilationUnitSearchOrderSim, TheUnitsTri1ReadsOneUndriven) {
  EXPECT_EQ(RunAndGet("tri1 w;\n"
                      "module top;\n"
                      "  logic y;\n"
                      "  initial #1 y = (w === 1'b1);\n"
                      "endmodule\n",
                      "y"),
            1u);
}

TEST(CompilationUnitSearchOrderSim, AModulesOwnNetKeepsItsDriverFromTheUnits) {
  EXPECT_EQ(RunAndGet("wire w;\n"
                      "module sub;\n"
                      "  wire w;\n"
                      "  assign w = 1'b1;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  logic y;\n"
                      "  sub s();\n"
                      "  initial #1 y = (w === 1'bz);\n"
                      "endmodule\n",
                      "y"),
            1u);
}

}  // namespace
