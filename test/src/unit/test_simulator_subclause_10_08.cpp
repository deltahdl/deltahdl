#include <gtest/gtest.h>

#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AssignmentLikeContextSim, ProceduralAssignExtendsInAssignLikeContext) {
  SimFixture f;
  auto* wide = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] wide;\n"
      "  initial begin\n"
      "    wide = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(wide->value.ToUint64(), 0x000Au);
}

TEST(AssignmentLikeContextSim, NBAAssignLikeContext) {
  SimFixture f;
  auto* narrow = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial narrow <= 8'hFF;\n"
      "endmodule\n",
      f, "narrow");
  ASSERT_NE(narrow, nullptr);
  EXPECT_EQ(narrow->value.ToUint64(), 0xFu);
}

TEST(AssignmentLikeContextSim, ContAssignExtendsInAssignLikeContext) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [15:0] result;\n"
                      "  logic [3:0] narrow = 4'hA;\n"
                      "  assign result = narrow;\n"
                      "endmodule\n",
                      "result"),
            0x000Au);
}

TEST(AssignmentLikeContextSim, ContAssignTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [3:0] result;\n"
                      "  logic [15:0] wide = 16'hCAFE;\n"
                      "  assign result = wide;\n"
                      "endmodule\n",
                      "result"),
            0xEu);
}

TEST(AssignmentLikeContextSim, ParameterExplicitTypeTruncatesValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  parameter logic [7:0] P = 16'hCAFE;\n"
                      "  logic [7:0] result;\n"
                      "  initial result = P;\n"
                      "endmodule\n",
                      "result"),
            0xFEu);
}

TEST(AssignmentLikeContextSim, ParameterExplicitTypeExtendsValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  parameter logic [15:0] P = 4'hA;\n"
                      "  logic [15:0] result;\n"
                      "  initial result = P;\n"
                      "endmodule\n",
                      "result"),
            0x000Au);
}

TEST(AssignmentLikeContextSim, ParameterOverrideInInstanceTruncates) {
  EXPECT_EQ(
      RunAndGet(
          "module inner #(parameter logic [7:0] P = 0)(output logic [7:0] o);\n"
          "  assign o = P;\n"
          "endmodule\n"
          "module t;\n"
          "  logic [7:0] result;\n"
          "  inner #(.P(16'hCAFE)) u(.o(result));\n"
          "endmodule\n",
          "result"),
      0xFEu);
}

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
  EXPECT_EQ(
      RunAndGet("module inner(input logic [3:0] i, output logic [3:0] o);\n"
                "  assign o = i;\n"
                "endmodule\n"
                "module t;\n"
                "  logic [7:0] wide = 8'hAB;\n"
                "  logic [3:0] result;\n"
                "  inner u(.i(wide), .o(result));\n"
                "endmodule\n",
                "result"),
      0xBu);
}

TEST(AssignmentLikeContextSim, SubroutineArgAssignLikeContext) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "module t;\n"
      "  function logic [7:0] trunc(logic [7:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  logic [7:0] result;\n"
      "  initial result = trunc(16'hCAFE);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);

  EXPECT_EQ(result->value.ToUint64(), 0xFEu);
}

TEST(AssignmentLikeContextSim, OutputArgTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  task set_val(output logic [7:0] o);\n"
                      "    o = 16'hCAFE;\n"
                      "  endtask\n"
                      "  logic [7:0] result;\n"
                      "  initial set_val(result);\n"
                      "endmodule\n",
                      "result"),
            0xFEu);
}

TEST(AssignmentLikeContextSim, InoutArgTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  task modify(inout logic [7:0] x);\n"
                      "    x = 16'hCAFE;\n"
                      "  endtask\n"
                      "  logic [7:0] result;\n"
                      "  initial begin\n"
                      "    result = 0;\n"
                      "    modify(result);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0xFEu);
}

TEST(AssignmentLikeContextSim, ReturnStatementAssignLikeContext) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "module t;\n"
      "  function logic [7:0] get_val();\n"
      "    return 32'hABCD;\n"
      "  endfunction\n"
      "  logic [7:0] result;\n"
      "  initial result = get_val();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 0xCDu);
}

TEST(AssignmentLikeContextSim, TaggedUnionExprTruncatesInAssignLikeContext) {
  EXPECT_EQ(
      RunAndGet(
          "module t;\n"
          "  typedef union tagged { logic [7:0] Small; logic [15:0] Big; } U;\n"
          "  U u;\n"
          "  int result;\n"
          "  initial begin\n"
          "    u = tagged Small (16'hCAFE);\n"
          "    result = u.Small;\n"
          "  end\n"
          "endmodule\n",
          "result"),
      0xFEu);
}

TEST(AssignmentLikeContextSim, ParenExprInAssignLikeContext) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial a = (16'hDEAD);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xADu);
}

TEST(AssignmentLikeContextSim, ConditionalExprInAssignLikeContext) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  logic sel = 1;\n"
      "  initial result = sel ? 16'hCAFE : 16'hBEEF;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);

  EXPECT_EQ(result->value.ToUint64(), 0xFEu);
}

TEST(AssignmentLikeContextSim, MintypMaxTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] result;\n"
                      "  initial result = (16'hDEAD : 16'hBEEF : 16'hCAFE);\n"
                      "endmodule\n",
                      "result"),
            0xEFu);
}

TEST(AssignmentLikeContextSim, NestedParenInConditionalPropagatesContext) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] result;\n"
                      "  logic sel = 1;\n"
                      "  initial result = sel ? (16'hCAFE) : (16'hBEEF);\n"
                      "endmodule\n",
                      "result"),
            0xFEu);
}

TEST(AssignmentLikeContextSim, NondefaultCorrespondenceTruncatesToFieldWidth) {
  EXPECT_EQ(
      RunAndGet(
          "module t;\n"
          "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
          "  ab_t s;\n"
          "  logic [7:0] result;\n"
          "  initial begin\n"
          "    s = '{a: 16'hCAFE, b: 8'h22};\n"
          "    result = s.a;\n"
          "  end\n"
          "endmodule\n",
          "result"),
      0xFEu);
}

TEST(AssignmentLikeContextSim, StaticCastTruncatesInAssignLikeContext) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] result;\n"
                      "  initial result = 8'(16'hCAFE);\n"
                      "endmodule\n",
                      "result"),
            0xFEu);
}

TEST(AssignmentLikeContextSim, StaticCastExtendsInAssignLikeContext) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [15:0] result;\n"
                      "  initial result = 16'(4'hA);\n"
                      "endmodule\n",
                      "result"),
            0x000Au);
}

TEST(AssignmentLikeContextSim, PatternOnOutputPortReceivesMembers) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "module sub(output pair_t p);\n"
      "  assign p = '{8'h12, 8'h34};\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x, y;\n"
      "  sub u(.p('{x, y}));\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x12u);
  EXPECT_EQ(y->value.ToUint64(), 0x34u);
}

TEST(AssignmentLikeContextSim, PatternOnOutputArgumentReceivesMembers) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "typedef struct { logic [7:0] a, b; } ab_t;\n"
      "module m;\n"
      "  task automatic t(output ab_t s); s = '{8'h1, 8'h2}; endtask\n"
      "  logic [7:0] x, y;\n"
      "  initial t('{x, y});\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 1u);
  EXPECT_EQ(y->value.ToUint64(), 2u);
}

TEST(AssignmentLikeContextSim, PatternOverridesStructureParameter) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct packed { logic [7:0] a, b; } ab_t;\n"
      "module sub #(parameter ab_t P = '{8'h11, 8'h22});\n"
      "  ab_t q;\n"
      "  initial q = P;\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.P('{8'h33, 8'h44})) u();\n"
      "  sub d();\n"
      "endmodule\n",
      f, "u.q");
  auto* q = f.ctx.FindVariable("u.q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0x3344u);
  auto* kept = f.ctx.FindVariable("d.q");
  ASSERT_NE(kept, nullptr);
  EXPECT_EQ(kept->value.ToUint64(), 0x1122u);
}

TEST(AssignmentLikeContextSim, ClassScopeOverrideTruncatesAndTypesAPattern) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C #(parameter logic [7:0] P = 0); endclass\n"
                       "class C2 #(parameter int P[2] = '{0, 0}); endclass\n"
                       "module t;\n"
                       "  initial $display(\"%h %0d\", C#(9'h1FF)::P,\n"
                       "                   C2#('{1, 2})::P[1]);\n"
                       "endmodule\n",
                       f),
            "ff 2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLikeContextSim,
     ClassParameterValueAndOverrideTakeTheDeclaredType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class K #(parameter logic signed [7:0] P = 4'sb1000,\n"
                       "          parameter logic [3:0] R = 8'hAB);\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%h %h %h %h\", K#()::P, K#()::R,\n"
                       "                   K#(12'hABC)::P, K#(.R(2'b11))::R);\n"
                       "endmodule\n",
                       f),
            "f8 b bc 3\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLikeContextSim, InterfaceParameterValueAndOverrideTakeTheType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface I #(parameter logic [3:0] P = 8'hAB,\n"
                       "             parameter int Q[2] = '{3, 4});\n"
                       "endinterface\n"
                       "module t;\n"
                       "  I u1(); I #(.P(9'h1F7), .Q('{5, 6})) u2();\n"
                       "  initial $display(\"%h %0d %h %0d\", u1.P, u1.Q[1], "
                       "u2.P, u2.Q[1]);\n"
                       "endmodule\n",
                       f),
            "b 4 7 6\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLikeContextSim, ProgramParameterValueAndOverrideTakeTheType) {
  for (const auto& [instance, expected] :
       {std::pair{"  pr q();\n", "d 8\n"},
        std::pair{"  pr #(.P(12'h0E9), .Q('{1, 9})) q();\n", "9 9\n"}}) {
    const std::string kSrc =
        std::string(
            "program pr #(parameter logic [3:0] P = 8'hCD,\n"
            "             parameter int Q[2] = '{7, 8});\n"
            "  initial $display(\"%h %0d\", P, Q[1]);\n"
            "endprogram\n"
            "module t;\n") +
        instance + "endmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(kSrc, f), expected) << kSrc;
    EXPECT_FALSE(f.diag.HasErrors()) << kSrc;
  }
}

TEST(AssignmentLikeContextSim,
     InterfaceAndProgramPortConnectionsTruncateAndExtend) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface J(input logic [3:0] a, output logic [7:0] b);\n"
                 "  assign b = {4'hF, a};\n"
                 "endinterface\n"
                 "program pp(input logic [3:0] a, output logic [7:0] y);\n"
                 "  assign y = {a, a};\n"
                 "  initial #2 $display(\"%h\", a);\n"
                 "endprogram\n"
                 "module t;\n"
                 "  logic [3:0] w4; logic [15:0] w16;\n"
                 "  J j(.a(8'hAB), .b(w4));\n"
                 "  pp p(.a(8'hCD), .y(w16));\n"
                 "  initial #1 $display(\"%h %h %h\", j.a, w4, w16);\n"
                 "endmodule\n",
                 f),
      "b b 00dd\nd\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLikeContextSim,
     DISABLED_PatternConnectedToAnUnpackedArrayInputPort) {
  constexpr const char* kReadThroughTheInstance =
      "  initial #1 $display(\"%0d\", u.arr[1]);\n";
  for (const auto& [declaration, reader] :
       {std::pair{"module s(input var int arr[2]); endmodule\n",
                  kReadThroughTheInstance},
        std::pair{"interface s(input var int arr[2]); endinterface\n",
                  kReadThroughTheInstance},
        std::pair{"program s(input var int arr[2]);\n"
                  "  initial #1 $display(\"%0d\", arr[1]);\n"
                  "endprogram\n",
                  ""}}) {
    const std::string kSrc = std::string(declaration) +
                             "module t;\n"
                             "  s u(.arr('{1, 2}));\n" +
                             reader + "endmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(kSrc, f), "2\n") << kSrc;
    EXPECT_FALSE(f.diag.HasErrors()) << kSrc;
  }
}

}  // namespace
