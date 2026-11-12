#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

inline std::string DecodeAsciiBytes(const Logic4Vec& vec) {
  uint32_t nbytes = vec.width / 8;
  std::string out;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= vec.nwords) continue;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    if (ch != 0) out += ch;
  }
  return out;
}

TEST(UtilitySystemTaskTest, Typename) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameDefaultSigningRemoved) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("y", 32);
  var->is_signed = true;
  var->is_4state = false;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "y")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "int");
}

TEST(UtilitySystemTaskTest, TypenameSingleBitLogic) {
  SimFixture f;
  f.ctx.CreateVariable("flag", 1);
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "flag")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameSingleBitTwoState) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("b1", 1);
  var->is_4state = false;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "b1")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "bit");
}

TEST(UtilitySystemTaskTest, TypenameTwoStateSignedNarrowVector) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("by", 8);
  var->is_4state = false;
  var->is_signed = true;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "by")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "bit[7:0]");
}

TEST(UtilitySystemTaskTest, TypenameUnknownIdentifierFallback) {
  SimFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "no_such_var")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameNoArgsFallback) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$typename", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameDataTypeFormBuiltinKeyword) {
  SimFixture f;
  auto* expr = ParseExprFrom("$typename(int)", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "int");
}

TEST(UtilitySystemTaskTest, TypenameDataTypeFormPackedVector) {
  SimFixture f;
  auto* expr = ParseExprFrom("$typename(logic [7:0])", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic[7:0]");
}

TEST(UtilitySystemTaskTest, TypenameExpressionFormVectorEndToEnd) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial $display(\"%s\", $typename(data));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "logic[7:0]\n");
}

TEST(UtilitySystemTaskTest, TypenameExpressionOperandNotEvaluated) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [3:0] n;\n"
      "  initial begin\n"
      "    n = 4'hA;\n"
      "    $display(\"%s\", $typename(n));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "bit[3:0]\n");
}

TEST(UtilitySystemTaskTest, TypenameDistinguishesTypesForStringComparison) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic [3:0] c;\n"
      "  initial begin\n"
      "    $display(\"%s\", $typename(a));\n"
      "    $display(\"%s\", $typename(b));\n"
      "    $display(\"%s\", $typename(c));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "logic[7:0]\nlogic[7:0]\nlogic[3:0]\n");
}

TEST(TypenameSim, AStringParameterInitializedByTypenameHoldsTheName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter string P = $typename(int);\n"
                       "  localparam string L = $typename(real);\n"
                       "  initial $display(\"[%s] [%s] %0d\", P, L, P == "
                       "\"int\");\n"
                       "endmodule\n",
                       f),
            "[int] [real] 1\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(TypenameSim, ATypedefNameResolvesToTheTypeItNames) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package A;\n"
                       "  typedef bit node;\n"
                       "endpackage\n"
                       "import A::*;\n"
                       "module top;\n"
                       "  node [2:0] Xv;\n"
                       "  initial begin\n"
                       "    $display(\"%s\", $typename(node));\n"
                       "    $display(\"%s\", $typename(Xv));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "bit\nbit[2:0]\n");
}

TEST(TypenameSim, APackageTypedefsRangeIsWrittenAsDeclared) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package A;\n"
                       "  typedef bit [9:1'b1] word;\n"
                       "endpackage\n"
                       "import A::*;\n"
                       "module top;\n"
                       "  word w;\n"
                       "  initial $display(\"%s\", $typename(w));\n"
                       "endmodule\n",
                       f),
            "bit[9:1]\n");
}

TEST(TypenameSim, AnEnumerationWritesItsConstantsAndScopedName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package A;\n"
                       "  enum {A, B, C = 99} X;\n"
                       "endpackage\n"
                       "import A::*;\n"
                       "module top;\n"
                       "  typedef enum {RED, GREEN = 5} col_t;\n"
                       "  col_t c;\n"
                       "  initial begin\n"
                       "    $display(\"%s\", $typename(X));\n"
                       "    $display(\"%s\", $typename(c));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "enum{A=32'sd0,B=32'sd1,C=32'sd99}A::e$X\n"
            "enum{RED=32'sd0,GREEN=32'sd5}top.col_t\n");
}

TEST(TypenameSim, AnEnumerationConstantIsSizedByItsBaseType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  typedef enum bit [1:0] {X, Y = 3} e_t;\n"
                       "  e_t v;\n"
                       "  initial $display(\"%s\", $typename(v));\n"
                       "endmodule\n",
                       f),
            "enum{X=2'd0,Y=2'd3}top.e_t\n");
}

TEST(TypenameSim, AStringVariableIsAString) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  string s;\n"
                       "  initial $display(\"%s\", $typename(s));\n"
                       "endmodule\n",
                       f),
            "string\n");
}

TEST(TypenameSim, AStructureWritesItsMembersAndScopedName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  typedef struct {bit A, B;} AB_t;\n"
                       "  AB_t AB[10];\n"
                       "  AB_t one;\n"
                       "  initial begin\n"
                       "    $display(\"%s\", $typename(AB));\n"
                       "    $display(\"%s\", $typename(one));\n"
                       "    $display(\"%s\", $typename(AB[2]));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "struct{bit A;bit B;}top.AB_t$[0:9]\n"
            "struct{bit A;bit B;}top.AB_t\nstruct{bit A;bit B;}top.AB_t\n");
}

TEST(TypenameSim, APropertyAndAFormalAreWrittenByTheirDeclaredTypes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  int n;\n"
                       "  bit [7:0] b;\n"
                       "  string q[$];\n"
                       "  function void show(real r);\n"
                       "    $display(\"%s %s %s %s\", $typename(n), "
                       "$typename(b), $typename(q[0]), $typename(r));\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  C c = new;\n"
                       "  initial c.show(1.0);\n"
                       "endmodule\n",
                       f),
            "int bit[7:0] string real\n");
}

TEST(TypenameSim, ATypeParameterNamesTheTypeItIsBoundTo) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C #(type T = int);\n"
                       "  function void show();\n"
                       "    $display(\"%s\", $typename(T));\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  C #() a = new;\n"
                       "  C #(bit [7:0]) b = new;\n"
                       "  initial begin\n"
                       "    a.show();\n"
                       "    b.show();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "int\nbit[7:0]\n");
}

TEST(TypenameSim, ASigningOtherThanTheDefaultIsWritten) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int unsigned a;\n"
                       "  byte unsigned b;\n"
                       "  time signed c;\n"
                       "  int signed d;\n"
                       "  bit signed [3:0] e;\n"
                       "  initial $display(\"%s|%s|%s|%s|%s\", $typename(a),\n"
                       "      $typename(b), $typename(c), $typename(d),\n"
                       "      $typename(e));\n"
                       "endmodule\n",
                       f),
            "int unsigned|byte unsigned|time signed|int|bit signed[3:0]\n");
}

TEST(TypenameSim, AClassHandleIsOfItsScopedClass) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class R; endclass\n"
                       "module t;\n"
                       "  R y;\n"
                       "  initial $display(\"%s\", $typename(y));\n"
                       "endmodule\n",
                       f),
            "$unit::R\n");
}

TEST(TypenameSim, AnExpressionIsOfItsSelfDeterminedType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  bit [7:0] a;\n"
                       "  bit [3:0] b;\n"
                       "  initial begin\n"
                       "    $display(\"%s\", $typename(a + b));\n"
                       "    $display(\"%s\", $typename({a, b}));\n"
                       "    $display(\"%s\", $typename(a[5:2]));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "bit[7:0]\nbit[11:0]\nbit[3:0]\n");
}

TEST(TypenameSim, AnExpressionTakesItsStateSignAndWidthFromItsOperands) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [3:0] l;\n"
                       "  bit [3:0] b;\n"
                       "  bit [7:0] a;\n"
                       "  int i;\n"
                       "  byte s;\n"
                       "  real r;\n"
                       "  initial begin\n"
                       "    $display(\"%s\", $typename(l & b));\n"
                       "    $display(\"%s\", $typename(i + s));\n"
                       "    $display(\"%s\", $typename(~s));\n"
                       "    $display(\"%s\", $typename(l == b));\n"
                       "    $display(\"%s\", $typename(!b));\n"
                       "    $display(\"%s\", $typename(a << b));\n"
                       "    $display(\"%s\", $typename(a[3+:2]));\n"
                       "    $display(\"%s\", $typename(a[0]));\n"
                       "    $display(\"%s\", $typename(a + r));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "logic[3:0]\nbit signed[31:0]\nbit signed[7:0]\nlogic\nbit\n"
            "bit[7:0]\nbit[1:0]\nbit\nreal\n");
}

TEST(TypenameSim, ASelectOfAPackedArrayIsOfItsElementsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [3:0][7:0] p;\n"
                       "  bit [3:0] n;\n"
                       "  initial begin\n"
                       "    $display(\"%s\", $typename(p[1]));\n"
                       "    $display(\"%s\", $typename(p[2:1]));\n"
                       "    $display(\"%s\", $typename(p[1] + n));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "logic[7:0]\nlogic[15:0]\nlogic[7:0]\n");
}

TEST(UtilitySystemTaskTest, TypenameOfAnExpressionOverAnUnknownNameFallsBack) {
  SimFixture f;
  auto* expr = ParseExprFrom("$typename(no_such_var + 1)", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(TypenameSim,
     DISABLED_AModuleInterfaceOrProgramTypeParameterNamesItsBoundType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface I #(parameter type T = int);\n"
                       "  initial #1 $display(\"I %s\", $typename(T));\n"
                       "endinterface\n"
                       "program P #(parameter type T = shortint);\n"
                       "  initial #3 $display(\"P %s\", $typename(T));\n"
                       "endprogram\n"
                       "module m #(parameter type T = logic [7:0]);\n"
                       "  parameter type B = shortint;\n"
                       "  localparam type L = byte;\n"
                       "  initial #2 $display(\"m %s %s %s\", $typename(T), "
                       "$typename(B), $typename(L));\n"
                       "endmodule\n"
                       "module t;\n"
                       "  I #(.T(bit [3:0])) i(); P p(); m u();\n"
                       "  m #(.T(int)) v();\n"
                       "endmodule\n",
                       f),
            "I bit[3:0]\nm logic[7:0] shortint byte\nm int shortint byte\nP "
            "shortint\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
