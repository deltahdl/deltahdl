#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §3.12.1 (printed page 56) searches for an identifier first in the scope
// that holds it, then in the part of the compilation-unit scope written before
// it, and only then up the instance hierarchy. A task's local b is its own:
// the task writes and reads it, 2, while the unit's b keeps 1, so
// `y * 10 + $unit::b` is 21. Resolved in the unit, both read 2: 22.
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

// The compilation-unit scope is searched before the instance hierarchy, so a
// child calling f, which neither it nor its own scope declares, runs the
// unit's f, 1, not the f of the module instantiating it, 2.
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

// §3.12.1 (printed page 57): `$unit::` names the compilation-unit scope's own
// declaration past a nearer one of the name. The unit task's local b is 0 when
// `b = 5 + $unit::b;` runs, and $unit::b is the unit's 1, so the local becomes
// 6; read as the local, it became 5.
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

// §3.12.1 (printed page 57): `$unit::` names the compilation unit's own
// subroutine past one of the name the calling scope declares, where the bare
// name calls the nearer one. Called from a module, a module function's body
// and a generate block, each declaring its own f returning 2, `$unit::f()` is
// the unit's 1 and `f()` the scope's own, so each reads 12; a `$unit::` call
// bound like the bare one reads 22.
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

// The same for a task, enabled as `$unit::t;` and as `$unit::t();`: both run
// the unit's t, counting hits twice, and the module's own t, which would add
// 10 to own each time, never runs, so y is 200; bound to the module's, 20.
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

// §3.12.1 (printed page 56) searches the nested scopes first, nested module
// declarations among them (§23.4), and the compilation-unit scope after. A
// module declared inside outer reads outer's x, 2, ahead of the unit's 1.
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

// The search goes outward through each enclosing declaration: a module two
// levels in, whose own enclosing module declares neither name, reaches the
// outermost one's x and f, 20 and 2, ahead of the unit's 10 and 1, so y is 22.
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

// The nearest allowed form: the nested module's own declaration of the name,
// a variable or a function, is found before the enclosing module's and the
// unit's, so y is 3.
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

// The design the cases below run: a top whose x and w are 7, instantiating
// holder, which has an instance of its own named top, a leaf whose x and w
// are 3.
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

// The run's value of h.y after holder, past its declarations `decls`, runs
// `stmt` at time 1.
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

// §3.12.1 (printed page 56): for upward name referencing the compilation-unit
// scope is a top-level design element, so a hierarchical name a unit task,
// function or class method writes is a full path from $root. Called from
// holder, whose own leaf instance is named top, each reads the top module's
// x, 7, never holder's top.x, 3.
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

// A net the path reaches is the top module's as a variable is: w, 7.
TEST(CompilationUnitSearchOrderSim, AUnitFunctionsPathToANetIsReadFromRoot) {
  EXPECT_EQ(HolderRuns("function int f();\n"
                       "  return top.w;\n"
                       "endfunction\n",
                       "", "y = f();"),
            7u);
}

// The nearest allowed form: a dotted name headed by the unit's own variable is
// no path at all but a member of that variable, so the unit's s.a, 4, is read
// whatever structure of the name the top declares.
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

// §3.12.1 (printed page 56): a net declaration is an item a package may hold,
// so the compilation unit may hold one, and a module reaches it by its bare
// name: the module's continuous assignment drives the unit's w, and its read
// of w a time step later sees the 1 driven.
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

// The unit's net is one net for every module that reaches it: an instance
// drives all eight bits of the unit's w, and the top reads 8'hA5 from it.
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

// The unit's net resolves by the net type it was declared with (§6.6.3): two
// instances drive 1 and 0 onto the unit's wand, which reads 0 where a wire
// would read x.
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

// A pulled net of the unit holds its pull with nothing driving it (§6.6.5):
// the unit's tri1 reads 1 where a wire would read z.
TEST(CompilationUnitSearchOrderSim, TheUnitsTri1ReadsOneUndriven) {
  EXPECT_EQ(RunAndGet("tri1 w;\n"
                      "module top;\n"
                      "  logic y;\n"
                      "  initial #1 y = (w === 1'b1);\n"
                      "endmodule\n",
                      "y"),
            1u);
}

// The nearest form the search does not reach: a module declaring a net of the
// name drives its own, so the unit's w, which the top reads, stays z.
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
