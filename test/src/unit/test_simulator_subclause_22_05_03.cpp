#include "helpers_preprocess_and_get.h"

// §22.5.3 `undefineall, observed after the full preprocess -> parse ->
// elaborate -> simulate pipeline: the macros the directive removes are built
// with the real `define syntax of §22.5.1 and the surviving value is read out
// of the simulated design.

// WITNESS is defined before the directive and never defined again, so the
// `ifdef proves the removal happened; redefining VAL alone would not, since a
// plain redefinition overwrites the old body anyway.
TEST(UndefineAllSimulation, UndefineAllThenRedefineSimulatesNewValue) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd10\n"
      "`define WITNESS\n"
      "`undefineall\n"
      "`define VAL 8'd55\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef WITNESS\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = `VAL;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 55u);
}

TEST(UndefineAllSimulation, UndefineAllExcludesConditionalFromSimulation) {
  auto result = PreprocessAndGet(
      "`define USE_ALT\n"
      "`undefineall\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = 8'd22;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 22u);
}

// A function-like macro is removed just like an object-like one, so the value
// that reaches the simulation is the one defined after the directive.
TEST(UndefineAllSimulation, UndefineAllRemovesFunctionLikeMacro) {
  auto result = PreprocessAndGet(
      "`define PICK(a, b) a\n"
      "`define WITNESS\n"
      "`undefineall\n"
      "`define PICK(a, b) b\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef WITNESS\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = `PICK(8'd3, 8'd77);\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

// A macro carrying an argument default is removed whole, defaults included, so
// the name no longer selects the wide branch and the later definition supplies
// the value that reaches the simulation.
TEST(UndefineAllSimulation, UndefineAllRemovesMacroWithArgumentDefaults) {
  auto result = PreprocessAndGet(
      "`define SCALE(a = 8'd5) a\n"
      "`define WITNESS\n"
      "`undefineall\n"
      "`define SCALE(a = 8'd88) a\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef WITNESS\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = `SCALE();\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 88u);
}

// An escaped identifier is an equally valid macro name, and a macro held under
// one is removed the same way. WITNESS proves the removal; the escaped name
// then supplies the value through its later definition.
TEST(UndefineAllSimulation, UndefineAllRemovesEscapedIdentifierMacro) {
  auto result = PreprocessAndGet(
      "`define \\VAL@ESC 8'd10\n"
      "`define WITNESS\n"
      "`undefineall\n"
      "`define \\VAL@ESC 8'd23\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef WITNESS\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = `\\VAL@ESC ;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 23u);
}

// A `undefineall the conditional compiled away never runs, so the macro it
// would have removed still drives the simulated value.
TEST(UndefineAllSimulation, UndefineAllInFalseBranchLeavesMacroUsable) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd44\n"
      "`ifdef NEVER_DEFINED\n"
      "`undefineall\n"
      "`endif\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 44u);
}

// C2 end to end: the directive takes no arguments, so real source sharing its
// line is not swallowed as one — it reaches the design and drives the result.
TEST(UndefineAllSimulation, UndefineAllTrailingSameLineTextReachesTheDesign) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd10\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`undefineall initial result = 8'd12;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

// C3 end to end: the directive is legal inside a procedural block, and the
// macro it removed there no longer selects the assignment.
TEST(UndefineAllSimulation, UndefineAllInsideProceduralBlockRemovesMacro) {
  auto result = PreprocessAndGet(
      "`define USE_ALT\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "`undefineall\n"
      "  end\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = 8'd33;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

// `undefineall_saved is a macro usage rather than the directive, so the macro
// it expands to supplies the value and the other macros survive.
TEST(UndefineAllSimulation, LongerNameStartingWithUndefineallExpandsAsMacro) {
  auto result = PreprocessAndGet(
      "`define WIDTH 8\n"
      "`define undefineall_saved 8'd66\n"
      "module t;\n"
      "  logic [`WIDTH-1:0] result;\n"
      "  initial result =\n"
      "`undefineall_saved\n"
      "    ;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 66u);
}
