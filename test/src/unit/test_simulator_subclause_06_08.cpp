#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(VariableDeclaration, VariableCreation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
}

TEST(VariableDeclaration, MultipleVariableCreation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindVariable("a"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("b"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("c"), nullptr);
}

TEST(VariableDeclaration, Logic4StateDefaultInit) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("data");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(VariableDeclaration, Logic4StateArrayElementDefaultInit) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(VariableDeclaration, ArrayElementDefaultXMatchesScalarDefaultX) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [7:0] arr [0:2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* scalar = f.ctx.FindVariable("data");
  auto* element = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(scalar, nullptr);
  ASSERT_NE(element, nullptr);

  ASSERT_EQ(element->value.nwords, scalar->value.nwords);
  EXPECT_EQ(element->value.words[0].aval, scalar->value.words[0].aval);
  EXPECT_EQ(element->value.words[0].bval, scalar->value.words[0].bval);
}

TEST(VariableDeclaration, Bit2StateArrayElementDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] arr [0:2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0u);
}

TEST(VariableDeclaration, Int2StateDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(VariableDeclaration, Bit2StateDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
}

TEST(VariableDeclaration, RealDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(VariableDeclaration, ShortrealDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortreal sr;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("sr");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(VariableDeclaration, StaticInitializerAppliesBeforeInitialBlock) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 42;\n"
      "  int observed;\n"
      "  initial observed = x;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, ChandleDefaultIsNull) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("h");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(VariableDeclaration, StringDefaultIsRegisteredAsString) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  string s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(f.ctx.IsStringVariable("s"));
}

TEST(VariableDeclaration, EventDefaultIsNewEvent) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("e");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_event);
  EXPECT_FALSE(var->is_null_event);
}

TEST(VariableDeclaration, StaticInitializerWithBinaryExpression) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 10 * 4 + 2;\n"
      "  int observed;\n"
      "  initial observed = x;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, StaticInitializerReferencesEarlierStatic) {
  auto val = RunAndGet(
      "module t;\n"
      "  int base = 7;\n"
      "  int derived = base * 6;\n"
      "  int observed;\n"
      "  initial observed = derived;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, StaticInitializerWithClassNew) {
  auto val = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int initial_v);\n"
      "    v = initial_v;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C handle = new(42);\n"
      "  int observed;\n"
      "  initial observed = handle.v;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration,
     EnumImplicitBaseDefaultsToBaseTypeZeroNotFirstMember) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  enum { A = 5, B } e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("e");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(VariableDeclaration, Enum4StateBaseDefaultsToX) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  enum logic [1:0] { A, B } e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("e");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].bval & 0x3u, 0x3u);
}

TEST(VariableDeclaration, ClassHandleDefaultIsNull) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int v;\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("h");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(VariableDeclaration, VariableStoresValueBetweenAssignmentAndRead) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    x = 99;\n"
      "    observed = x;\n"
      "  end\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 99u);
}

TEST(VariableDeclaration,
     KeyedPatternUncoveredElementTakesItsDefaultInitialValue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a [0:2] = '{int: 8'h05};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("a[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            2, "10.9.1"));
}

TEST(VariableDeclaration,
     KeyedPatternStatementUncoveredElementTakesItsDefaultInitialValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a [0:2];\n"
      "  initial a = '{int: 8'h05};\n"
      "endmodule\n",
      f, "a[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            3, "10.9.1"));
}

TEST(VariableDeclaration, Logic4StateSubroutineLocalDefaultsToX) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  function automatic void fa();\n"
          "    logic l; logic [3:0] v; int n; string s; real r;\n"
          "    $display(\"fa: l=%0h v=%b n=%0d s=[%s] r=%f\", l, v, n, s,"
          " r);\n"
          "  endfunction\n"
          "  task automatic ta();\n"
          "    logic l;\n"
          "    $display(\"ta: l=%0h\", l);\n"
          "  endtask\n"
          "  function void fs();\n"
          "    logic [3:0] i;\n"
          "    $display(\"fs: i=%b\", i);\n"
          "  endfunction\n"
          "  class C;\n"
          "    function void m();\n"
          "      logic l;\n"
          "      $display(\"m: l=%0h\", l);\n"
          "    endfunction\n"
          "  endclass\n"
          "  C c;\n"
          "  initial begin\n"
          "    fa(); ta(); fs(); c = new; c.m();\n"
          "  end\n"
          "endmodule\n",
          f),
      "fa: l=x v=xxxx n=0 s=[] r=0.000000\nta: l=x\nfs: i=xxxx\nm: l=x\n");
}

}  // namespace
