#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
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

std::string RunTypename(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(TypenameSim, DISABLED_AnEnumerationConstantIsOfItsEnumType) {
  EXPECT_EQ(
      RunTypename("package pk;\n"
                  "  typedef enum {PA, PB} pe_t;\n"
                  "endpackage\n"
                  "class Packet;\n"
                  "  typedef enum {OK, ERR_UNDERFLOW} err_t;\n"
                  "  function string own();\n"
                  "    return $typename(ERR_UNDERFLOW);\n"
                  "  endfunction\n"
                  "endclass\n"
                  "module top;\n"
                  "  typedef enum {A = 1, B} et;\n"
                  "  enum {X, Y} av;\n"
                  "  Packet p = new;\n"
                  "  initial begin\n"
                  "    $display(\"%s\", $typename(B));\n"
                  "    $display(\"%s\", $typename(pk::PB));\n"
                  "    $display(\"%0d\", $typename(Y) == $typename(av));\n"
                  "    $display(\"%0d\", $typename(Packet::ERR_UNDERFLOW) ==\n"
                  "      $typename(p.ERR_UNDERFLOW));\n"
                  "    $display(\"%0d\", p.own() ==\n"
                  "      $typename(Packet::ERR_UNDERFLOW));\n"
                  "    $display(\"%s\", $typename(p.ERR_UNDERFLOW));\n"
                  "  end\n"
                  "endmodule\n"),
      "enum{A=32'sd1,B=32'sd2}top.et\n"
      "enum{PA=32'sd0,PB=32'sd1}pk::pe_t\n1\n1\n1\n"
      "enum{OK=32'sd0,ERR_UNDERFLOW=32'sd1}$unit::Packet::err_t\n");
}

TEST(TypenameSim, AFunctionCallArgumentIsNeverCalled) {
  EXPECT_EQ(
      RunTypename("module top;\n"
                  "  int counter = 0;\n"
                  "  function int bump();\n"
                  "    counter++;\n"
                  "    return counter;\n"
                  "  endfunction\n"
                  "  initial begin\n"
                  "    $display(\"%0d\", $typename(bump()) == \"\");\n"
                  "    $display(\"%0d\", $typename(bump() + 1) == \"\");\n"
                  "    $display(\"%0d\", counter);\n"
                  "  end\n"
                  "endmodule\n"),
      "0\n0\n0\n");
}

TEST(TypenameSim, AWholeMultidimensionalArrayWritesEveryRange) {
  EXPECT_EQ(
      RunTypename("module top;\n"
                  "  int m[2][3];\n"
                  "  byte r[3:1][0:1];\n"
                  "  initial $display(\"%s %s\", $typename(m), $typename(r));\n"
                  "endmodule\n"),
      "int$[0:1][0:2] byte$[3:1][0:1]\n");
}

TEST(TypenameSim, DISABLED_AVariablySizedArrayWritesItsDimension) {
  EXPECT_EQ(
      RunTypename("module top;\n"
                  "  int d[];\n"
                  "  int q[$];\n"
                  "  int b[$:4];\n"
                  "  int a[string];\n"
                  "  int w[*];\n"
                  "  int i[int];\n"
                  "  initial begin\n"
                  "    $display(\"%s %s %s\", $typename(d), $typename(q),\n"
                  "      $typename(b));\n"
                  "    $display(\"%s %s %s\", $typename(a), $typename(w),\n"
                  "      $typename(i));\n"
                  "  end\n"
                  "endmodule\n"),
      "int$[] int$[$] int$[$:4]\nint$[string] int$[*] int$[int]\n");
}

TEST(TypenameSim, APredefinedWidthTypeDiffersFromItsSizedVector) {
  EXPECT_EQ(RunTypename(
                "module top;\n"
                "  int a; bit signed [31:0] b;\n"
                "  integer c; logic signed [31:0] d;\n"
                "  byte e; bit signed [7:0] g;\n"
                "  shortint h; bit signed [15:0] j;\n"
                "  longint k; bit signed [63:0] l;\n"
                "  initial begin\n"
                "    $display(\"%s|%s|%s|%s|%s\", $typename(a), $typename(c),\n"
                "      $typename(e), $typename(h), $typename(k));\n"
                "    $display(\"%s|%s|%s|%s|%s\", $typename(b), $typename(d),\n"
                "      $typename(g), $typename(j), $typename(l));\n"
                "    $display(\"%0d\", $typename(int) != $typename(bit signed "
                "[31:0]));\n"
                "  end\n"
                "endmodule\n"),
            "int|integer|byte|shortint|longint\n"
            "bit signed[31:0]|logic signed[31:0]|bit signed[7:0]|bit "
            "signed[15:0]|bit signed[63:0]\n1\n");
}

TEST(TypenameSim, DISABLED_AStringMethodCalledOnTheResultActsOnTheName) {
  EXPECT_EQ(
      RunTypename("module top;\n"
                  "  int n;\n"
                  "  initial $display(\"%0d %0d %s\", $typename(n).len(),\n"
                  "    $typename(logic [7:0]).len(), $typename(n).toupper());\n"
                  "endmodule\n"),
      "3 10 INT\n");
}

TEST(TypenameSim, AnExplicitDefaultSigningIsLeftOut) {
  EXPECT_EQ(
      RunTypename(
          "module top;\n"
          "  logic unsigned [3:0] a;\n"
          "  byte signed b;\n"
          "  integer signed c;\n"
          "  shortint signed d;\n"
          "  longint signed e;\n"
          "  bit unsigned [2:0] g;\n"
          "  initial begin\n"
          "    $display(\"%s|%s|%s|%s|%s|%s\", $typename(a), $typename(b),\n"
          "      $typename(c), $typename(d), $typename(e), $typename(g));\n"
          "    $display(\"%s|%s|%s\", $typename(int signed),\n"
          "      $typename(logic unsigned [3:0]), $typename(byte signed));\n"
          "  end\n"
          "endmodule\n"),
      "logic[3:0]|byte|integer|shortint|longint|bit[2:0]\n"
      "int|logic[3:0]|byte\n");
}

TEST(TypenameSim, DISABLED_ASignedNetKeepsItsSigning) {
  EXPECT_EQ(RunTypename(
                "module top (input signed [3:0] p);\n"
                "  wire logic signed ns;\n"
                "  wire logic nn;\n"
                "  wire signed [3:0] vs;\n"
                "  trireg signed [3:0] tr;\n"
                "  trireg (small) signed [3:0] cap2;\n"
                "  wire integer wi;\n"
                "  initial begin\n"
                "    $display(\"%s|%s|%s|%s\", $typename(ns), $typename(nn),\n"
                "      $typename(vs), $typename(tr));\n"
                "    $display(\"%s|%s|%s\", $typename(cap2), $typename(wi),\n"
                "      $typename(p));\n"
                "  end\n"
                "endmodule\n"),
            "logic signed|logic|logic signed[3:0]|logic signed[3:0]\n"
            "logic signed[3:0]|integer|logic signed[3:0]\n");
}

TEST(TypenameSim, DISABLED_ASignedNetOfEveryNetTypeKeepsItsSigning) {
  EXPECT_EQ(RunTypename(
                "module top;\n"
                "  tri signed [1:0] a;\n"
                "  wand signed [1:0] b;\n"
                "  wor signed [1:0] c;\n"
                "  triand signed [1:0] d;\n"
                "  trior signed [1:0] e;\n"
                "  tri0 signed [1:0] g;\n"
                "  tri1 signed [1:0] h;\n"
                "  uwire signed [1:0] i;\n"
                "  supply0 signed [1:0] j;\n"
                "  supply1 signed [1:0] k;\n"
                "  initial $display(\"%s|%s|%s|%s|%s|%s|%s|%s|%s|%s\",\n"
                "    $typename(a), $typename(b), $typename(c), $typename(d),\n"
                "    $typename(e), $typename(g), $typename(h), $typename(i),\n"
                "    $typename(j), $typename(k));\n"
                "endmodule\n"),
            "logic signed[1:0]|logic signed[1:0]|logic signed[1:0]|logic "
            "signed[1:0]|logic signed[1:0]|logic signed[1:0]|logic "
            "signed[1:0]|logic signed[1:0]|logic signed[1:0]|logic "
            "signed[1:0]\n");
}

TEST(TypenameSim, DISABLED_ALiteralAndACallAreOfTheirSelfDeterminedTypes) {
  std::string out = RunTypename(
      "module top;\n"
      "  function int fi();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  function byte fb();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    $display(\"%s\", $typename(0));\n"
      "    $display(\"%s|%s\", $typename(fi()), $typename(fb()));\n"
      "  end\n"
      "endmodule\n");
  auto newline = out.find('\n');
  ASSERT_NE(newline, std::string::npos) << out;
  std::string literal = out.substr(0, newline);
  EXPECT_TRUE(literal == "int" || literal == "integer" ||
              literal == "logic signed[31:0]")
      << literal;
  EXPECT_EQ(out.substr(newline + 1), "int|byte\n");
}

TEST(TypenameSim, AnUnresolvedNameIsReported) {
  SimFixture f;
  RunCapture(
      "module top;\n"
      "  initial begin\n"
      "    $display(\"%s\", $typename(no_such_var));\n"
      "    $display(\"%s\", $typename(no_such_var + 1));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'no_such_var'",
                            3, "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'no_such_var'",
                            4, "23.9"));
}

TEST(TypenameSim, AnonymousUnionsAndUnpackedStructsGetGeneratedNames) {
  EXPECT_EQ(RunTypename("module top;\n"
                        "  union {int a; bit b;} u;\n"
                        "  struct {bit a; byte b;} s;\n"
                        "  initial begin\n"
                        "    $display(\"%s\", $typename(u));\n"
                        "    $display(\"%s\", $typename(union {int a;}));\n"
                        "    $display(\"%s\", $typename(s));\n"
                        "  end\n"
                        "endmodule\n"),
            "union{int a;bit b;}top.u$u\nunion{int a;}top.u$type\n"
            "struct{bit a;byte b;}top.s$s\n");
}

TEST(TypenameSim, APackageTypeIsPrefixedWithItsPackage) {
  EXPECT_EQ(RunTypename("package A;\n"
                        "  typedef struct {bit a; byte b;} ps_t;\n"
                        "endpackage\n"
                        "module top;\n"
                        "  A::ps_t s;\n"
                        "  initial $display(\"%s\", $typename(s));\n"
                        "endmodule\n"),
            "struct{bit a;byte b;}A::ps_t\n");
}

TEST(TypenameSim, DISABLED_AScopedTypeNamedAsTheArgumentIsPrefixed) {
  EXPECT_EQ(RunTypename("package A;\n"
                        "  typedef struct {bit a; byte b;} ps_t;\n"
                        "  typedef enum {M, N} pe_t;\n"
                        "endpackage\n"
                        "class R; endclass\n"
                        "module top;\n"
                        "  initial begin\n"
                        "    $display(\"%s\", $typename(A::ps_t));\n"
                        "    $display(\"%s\", $typename(A::pe_t));\n"
                        "    $display(\"%s\", $typename(R));\n"
                        "  end\n"
                        "endmodule\n"),
            "struct{bit a;byte b;}A::ps_t\nenum{M=32'sd0,N=32'sd1}A::pe_t\n"
            "$unit::R\n");
}

TEST(TypenameSim, DISABLED_AClassScopedTypedefIsWrittenOutBehindItsClass) {
  EXPECT_EQ(
      RunTypename("class K;\n"
                  "  typedef struct {bit x;} ks_t;\n"
                  "  typedef enum {P, Q} ke_t;\n"
                  "endclass\n"
                  "module top;\n"
                  "  K::ks_t k;\n"
                  "  K::ke_t e;\n"
                  "  initial begin\n"
                  "    $display(\"%s\", $typename(k));\n"
                  "    $display(\"%s\", $typename(e));\n"
                  "    $display(\"%s\", $typename(K::ks_t));\n"
                  "  end\n"
                  "endmodule\n"),
      "struct{bit x;}$unit::K::ks_t\nenum{P=32'sd0,Q=32'sd1}$unit::K::ke_t\n"
      "struct{bit x;}$unit::K::ks_t\n");
}

TEST(TypenameSim, DISABLED_AnInterfaceOrProgramTypeIsPrefixedWithItsOwnScope) {
  EXPECT_EQ(RunTypename("interface I;\n"
                        "  typedef struct {bit y;} is_t;\n"
                        "  is_t v;\n"
                        "  initial #1 $display(\"%s\", $typename(v));\n"
                        "endinterface\n"
                        "program P;\n"
                        "  typedef struct {bit z;} pg_t;\n"
                        "  pg_t w;\n"
                        "  initial #2 $display(\"%s\", $typename(w));\n"
                        "endprogram\n"
                        "module top;\n"
                        "  I i();\n"
                        "  P p();\n"
                        "endmodule\n"),
            "struct{bit y;}top.i.is_t\nstruct{bit z;}top.p.pg_t\n");
}

TEST(TypenameSim, ATypedefOfATypedefResolvesToTheInnerStructure) {
  EXPECT_EQ(RunTypename("module top;\n"
                        "  typedef struct {bit a;} s1_t;\n"
                        "  typedef s1_t s2_t;\n"
                        "  s2_t v;\n"
                        "  initial begin\n"
                        "    $display(\"%s\", $typename(s2_t));\n"
                        "    $display(\"%s\", $typename(v));\n"
                        "  end\n"
                        "endmodule\n"),
            "struct{bit a;}top.s1_t\nstruct{bit a;}top.s1_t\n");
}

TEST(TypenameSim, DISABLED_AClassScopedTypedefOfABuiltInTypeResolves) {
  EXPECT_EQ(
      RunTypename(
          "class C;\n"
          "  typedef bit [3:0] T;\n"
          "endclass\n"
          "module top;\n"
          "  C::T v;\n"
          "  initial $display(\"%s %s\", $typename(C::T), $typename(v));\n"
          "endmodule\n"),
      "bit[3:0] bit[3:0]\n");
}

}  // namespace
