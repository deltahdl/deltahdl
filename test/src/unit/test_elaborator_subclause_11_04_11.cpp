#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ConstEval, TernarySelectsCorrectBranch) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 ? 42 : 99", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ? 42 : 99", f)), 99);
}

TEST(ConstEval, ScopedTernary) {
  EvalFixture f;
  ScopeMap scope_big = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_big),
            16);
  ScopeMap scope_small = {{"WIDTH", 4}};
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_small), 8);
}

TEST(ExpressionElaboration, TernaryInContAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel;\n"
      "  wire [7:0] a, b, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombBasicSim, AlwaysCombTernaryTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 1;\n"
      "  always_comb begin\n"
      "    result = sel ? 8'd42 : 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AlwaysCombBasicSim, AlwaysCombTernaryFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 0;\n"
      "  always_comb begin\n"
      "    result = sel ? 8'd42 : 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(AlwaysCombBasicSim, AlwaysCombChainedTernary) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 2'd1;\n"
      "  always_comb begin\n"
      "    result = (sel == 2'd0) ? 8'd10 :\n"
      "             (sel == 2'd1) ? 8'd20 :\n"
      "             (sel == 2'd2) ? 8'd30 : 8'd40;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(AlwaysLatchBasicSim, TernarySelectsFirst) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 8'hCA;\n"
      "    b = 8'hFE;\n"
      "  end\n"
      "  always_latch\n"
      "    q = sel ? a : b;\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xCAu);
}

TEST(AlwaysLatchBasicSim, TernarySelectsSecond) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    a = 8'hCA;\n"
      "    b = 8'hFE;\n"
      "  end\n"
      "  always_latch\n"
      "    q = sel ? a : b;\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xFEu);
}

TEST(BlockingAssignSim, BlockingAssignTernary) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    result = sel ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(BlockingAssignSim, BlockingAssignTernaryFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    result = sel ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ConstEvalReal, TernaryOnReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("1 ? 2.5 : 3.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 2.5);
}

TEST(ExpressionElaboration, TernaryWidthIsMaxOfBranches) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    narrow = 4'hF;\n"
      "    wide = 8'hAA;\n"
      "    result = 1 ? narrow : wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(ExpressionElaboration, TernaryWidthEqualBranches) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "    result = 1 ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(ExpressionElaboration, TernarySignedBothBranchesSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b;\n"
      "  int result;\n"
      "  assign result = 1 ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, TernaryUnsignedMixedSignedness) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int signed_val;\n"
      "  logic [31:0] unsigned_val;\n"
      "  logic [31:0] result;\n"
      "  assign result = 1 ? signed_val : unsigned_val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstEvalReal, TernaryFalseConditionSelectsSecondReal) {
  EvalFixture f;
  auto* e = ParseExprFrom("0 ? 2.5 : 3.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 3.5);
}

TEST(ConstEval, NestedTernaryConstEval) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 ? (0 ? 10 : 20) : 30", f)), 20);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ? 10 : (1 ? 20 : 30)", f)), 20);
}

TEST(ConstEval, ChainedTernaryConstEval) {
  EvalFixture f;
  ScopeMap scope = {{"SEL", 2}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("SEL == 0 ? 10 : SEL == 1 ? 20 : 30", f),
                         scope),
            30);
  scope["SEL"] = 1;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("SEL == 0 ? 10 : SEL == 1 ? 20 : 30", f),
                         scope),
            20);
}

TEST(ConditionalElaboration, TernaryWithBothBranchesNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C h;\n"
      "  logic sel;\n"
      "  initial h = sel ? null : null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConditionalElaboration, TernaryWithOneNullBranchElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a, b;\n"
      "  logic sel;\n"
      "  initial a = sel ? b : null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstEval, ParameterConditionSelectsFirstBranchInConstExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter SEL = 1;\n"
      "  localparam int R = SEL ? 7 : 9;\n"
      "  int result;\n"
      "  initial result = R;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(ConstEval, ParameterConditionSelectsSecondBranchInConstExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter SEL = 0;\n"
      "  localparam int R = SEL ? 7 : 9;\n"
      "  int result;\n"
      "  initial result = R;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(ConstEval, ParameterOperandsInConstantTernary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter A = 5;\n"
      "  parameter B = 6;\n"
      "  localparam int R = 1 ? A : B;\n"
      "  int result;\n"
      "  initial result = R;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(ConditionalOperatorElaboration, UnrelatedOperandTypesReported) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "class D extends A; endclass\n"
      "class E extends A; endclass\n"
      "module t;\n"
      "  typedef struct { int x; } s1_t;\n"
      "  typedef struct { int x; } s2_t;\n"
      "  A a, r; B b; D d; E e;\n"
      "  A arr [2];\n"
      "  mailbox m1, m2;\n"
      "  s1_t p, q; s2_t o;\n"
      "  int i;\n"
      "  logic s;\n"
      "  initial begin\n"
      "    r = s ? a : b;\n"
      "    p = s ? q : o;\n"
      "    r = s ? a : d;\n"
      "    r = s ? d : e;\n"
      "    r = s ? null : a;\n"
      "    r = s ? a : null;\n"
      "    r = s ? arr[0] : a;\n"
      "    r = s ? a : arr[1];\n"
      "    m1 = s ? m1 : m2;\n"
      "    p = s ? q : p;\n"
      "    i = s ? i : 1;\n"
      "    i = s ? 1 : i;\n"
      "    p = s ? q : i;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "conditional operands of class types 'A' and 'B' "
                            "share no base class",
                            15, "11.4.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the operands of a conditional operator shall be "
                            "of equivalent types",
                            16, "11.4.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the operands of a conditional operator shall be "
                            "of equivalent types",
                            27, "11.4.11"));
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.message.find("conditional op") != std::string::npos)
      EXPECT_TRUE(d.loc.line == 15 || d.loc.line == 16 || d.loc.line == 27)
          << d.loc.line;
  }
}

TEST(ConditionalOperatorElaboration,
     AggregateOperandsOfDifferentTypesReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int x; } s_t;\n"
      "  s_t p;\n"
      "  int a4 [4], a3 [3], b4 [4];\n"
      "  int i;\n"
      "  logic s;\n"
      "  initial begin\n"
      "    a4 = s ? a4 : a3;\n"
      "    p = s ? p : i;\n"
      "    p = s ? 1 : p;\n"
      "    i = s ? a4 : 2;\n"
      "    a4 = s ? a4 : b4;\n"
      "    i = s ? i : 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u, 10u, 11u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the operands of a conditional operator shall "
                              "be of equivalent types",
                              line, "11.4.11"));
  }
  for (uint32_t line : {12u, 13u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "the operands of a conditional operator shall "
                               "be of equivalent types",
                               line, "11.4.11"));
  }
}

TEST(ConditionalOperatorElaboration,
     DISABLED_ClassBesideAnInterfaceItImplementsIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "interface class IC; endclass\n"
      "class C implements IC; endclass\n"
      "module m;\n"
      "  bit s; IC ic, ic2; C c;\n"
      "  initial begin ic2 = s ? c : ic; ic2 = s ? ic : c; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConditionalOperatorElaboration,
     ClassBranchesAssignedToTheirCommonTypeAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class D extends A; endclass\n"
      "class E extends A; endclass\n"
      "class K;\n"
      "  function A pick(bit s, D d, E e); return s ? d : e; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  bit s; A a, a2; D d, d2; E e;\n"
      "  initial begin\n"
      "    a2 = s ? d : e; a2 = s ? d : a; a2 = s ? a : d;\n"
      "    d2 = s ? null : d; d2 = s ? d : null;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConditionalOperatorElaboration,
     DISABLED_ACommonBaseResultAssignedToADerivedHandleIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class D extends A; endclass\n"
      "class E extends A; endclass\n"
      "class K;\n"
      "  function D pick(bit s, D d, E e); D r; r = s ? d : e; return r; "
      "endfunction\n"
      "endclass\n"
      "module m;\n"
      "  bit s; A a; D d, d2; E e;\n"
      "  initial begin\n"
      "    d2 = s ? d : e;\n"
      "    d2 = s ? a : d;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const int kLine : {5, 10, 11}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "class handle assignment requires assignment compatible", kLine, "8.4"))
        << kLine;
  }
}

TEST(ConditionalOperatorElaboration,
     TwoImplementersOfOneInterfaceClassAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface class IC; endclass\n"
      "class C1 implements IC; endclass\n"
      "class C2 implements IC; endclass\n"
      "module m;\n"
      "  bit s; IC ic; C1 c1; C2 c2;\n"
      "  initial ic = s ? c1 : c2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "conditional operands of class types 'C1' and 'C2' "
                            "share no base class",
                            6, "11.4.11"));
}

TEST(ConditionalOperatorElaboration,
     DISABLED_ClassBranchesWithNoCommonTypeInASubroutineArgumentAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface class IC; endclass\n"
      "class C1 implements IC; endclass\n"
      "class C2 implements IC; endclass\n"
      "module m;\n"
      "  bit s, r; C1 c1; C2 c2;\n"
      "  function bit id(bit x); return x; endfunction\n"
      "  initial begin\n"
      "    $display(\"%b\", (s ? c1 : c2) == null);\n"
      "    r = id((s ? c1 : c2) == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const int kLine : {8, 9}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "conditional operands of class types 'C1' and "
                              "'C2' share no base class",
                              kLine, "11.4.11"))
        << kLine;
  }
}

TEST(ConditionalOperatorElaboration,
     AStringLocalparamConditionedOnAVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit v;\n"
      "  localparam string S = v ? \"a\" : \"b\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'S' initializer is not a constant expression", 3, "6.20.4"));
}

TEST(ConditionalOperatorElaboration,
     AStringLocalparamConditionedOnAParameterIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int N = 1;\n"
      "  localparam string S = N ? \"a\" : \"b\";\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
