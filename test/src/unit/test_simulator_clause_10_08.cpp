#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- Item 1: Continuous or procedural assignment ---

TEST(AssignmentLikeContextSim, ProceduralAssignExtendsInAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] wide;\n"
      "  initial begin\n"
      "    wide = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* wide = f.ctx.FindVariable("wide");
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(wide->value.ToUint64(), 0x000Au);
}

TEST(AssignmentLikeContextSim, NBAAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial narrow <= 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* narrow = f.ctx.FindVariable("narrow");
  ASSERT_NE(narrow, nullptr);
  EXPECT_EQ(narrow->value.ToUint64(), 0xFu);
}

TEST(AssignmentLikeContextSim, ContAssignExtendsInAssignLikeContext) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  logic [3:0] narrow = 4'hA;\n"
      "  assign result = narrow;\n"
      "endmodule\n",
      "result"), 0x000Au);
}

TEST(AssignmentLikeContextSim, ContAssignTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [3:0] result;\n"
      "  logic [15:0] wide = 16'hCAFE;\n"
      "  assign result = wide;\n"
      "endmodule\n",
      "result"), 0xEu);
}

// --- Item 2: Parameter with explicit type declaration ---

TEST(AssignmentLikeContextSim, ParameterExplicitTypeTruncatesValue) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  parameter logic [7:0] P = 16'hCAFE;\n"
      "  logic [7:0] result;\n"
      "  initial result = P;\n"
      "endmodule\n",
      "result"), 0xFEu);
}

TEST(AssignmentLikeContextSim, ParameterExplicitTypeExtendsValue) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  parameter logic [15:0] P = 4'hA;\n"
      "  logic [15:0] result;\n"
      "  initial result = P;\n"
      "endmodule\n",
      "result"), 0x000Au);
}

TEST(AssignmentLikeContextSim, ParameterOverrideInInstanceTruncates) {
  EXPECT_EQ(RunAndGet(
      "module inner #(parameter logic [7:0] P = 0)(output logic [7:0] o);\n"
      "  assign o = P;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  inner #(.P(16'hCAFE)) u(.o(result));\n"
      "endmodule\n",
      "result"), 0xFEu);
}

// --- Item 3: Port connection to input or output port ---

TEST(AssignmentLikeContextSim, OutputPortAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module inner(output logic [3:0] o);\n"
      "  initial o = 4'hA;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  inner u(.o(wide));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* wide = f.ctx.FindVariable("wide");
  if (wide) {
    EXPECT_EQ(wide->value.ToUint64() & 0xF, 0xAu);
  }
}

TEST(AssignmentLikeContextSim, InputPortConnectionTruncates) {
  EXPECT_EQ(RunAndGet(
      "module inner(input logic [3:0] i, output logic [3:0] o);\n"
      "  assign o = i;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] wide = 8'hAB;\n"
      "  logic [3:0] result;\n"
      "  inner u(.i(wide), .o(result));\n"
      "endmodule\n",
      "result"), 0xBu);
}

// --- Item 4: Passing a value to a subroutine input, output, or inout argument ---

TEST(AssignmentLikeContextSim, SubroutineArgAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function logic [7:0] trunc(logic [7:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  logic [7:0] result;\n"
      "  initial result = trunc(16'hCAFE);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);

  EXPECT_EQ(result->value.ToUint64(), 0xFEu);
}

TEST(AssignmentLikeContextSim, OutputArgTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  task set_val(output logic [7:0] o);\n"
      "    o = 16'hCAFE;\n"
      "  endtask\n"
      "  logic [7:0] result;\n"
      "  initial set_val(result);\n"
      "endmodule\n",
      "result"), 0xFEu);
}

TEST(AssignmentLikeContextSim, InoutArgTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  task modify(inout logic [7:0] x);\n"
      "    x = 16'hCAFE;\n"
      "  endtask\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    modify(result);\n"
      "  end\n"
      "endmodule\n",
      "result"), 0xFEu);
}

// --- Item 5: Return statement in a function ---

TEST(AssignmentLikeContextSim, ReturnStatementAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function logic [7:0] get_val();\n"
      "    return 32'hABCD;\n"
      "  endfunction\n"
      "  logic [7:0] result;\n"
      "  initial result = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 0xCDu);
}

// --- Item 6: Tagged union expression ---

TEST(AssignmentLikeContextSim, TaggedUnionExprTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  typedef union tagged { logic [7:0] Small; logic [15:0] Big; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged Small (16'hCAFE);\n"
      "    result = u.Small;\n"
      "  end\n"
      "endmodule\n",
      "result"), 0xFEu);
}

// --- Item 7: Recursive propagation for RHS in assignment-like context ---

TEST(AssignmentLikeContextSim, ParenExprInAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial a = (16'hDEAD);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xADu);
}

TEST(AssignmentLikeContextSim, ConditionalExprInAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  logic sel = 1;\n"
      "  initial result = sel ? 16'hCAFE : 16'hBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);

  EXPECT_EQ(result->value.ToUint64(), 0xFEu);
}

TEST(AssignmentLikeContextSim, MintypMaxTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = (16'hDEAD : 16'hBEEF : 16'hCAFE);\n"
      "endmodule\n",
      "result"), 0xEFu);
}

TEST(AssignmentLikeContextSim, NestedParenInConditionalPropagatesContext) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  logic sel = 1;\n"
      "  initial result = sel ? (16'hCAFE) : (16'hBEEF);\n"
      "endmodule\n",
      "result"), 0xFEu);
}

// --- Item 9: Static cast of an expression ---

TEST(AssignmentLikeContextSim, StaticCastTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'(16'hCAFE);\n"
      "endmodule\n",
      "result"), 0xFEu);
}

TEST(AssignmentLikeContextSim, StaticCastExtendsInAssignLikeContext) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  initial result = 16'(4'hA);\n"
      "endmodule\n",
      "result"), 0x000Au);
}

}  // namespace
