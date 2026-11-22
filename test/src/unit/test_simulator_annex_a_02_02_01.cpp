#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(NetAndVariableTypeSimulation, IntegerVectorTypeLogicRuntimeWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hAB;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(NetAndVariableTypeSimulation, IntegerAtomByteRuntimeWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte b;\n"
      "  initial b = 8'h7F;\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(NetAndVariableTypeSimulation, IntegerAtomIntRuntimeWidth) {
  auto val = RunAndGet(
      "module t;\n"
      "  int i;\n"
      "  initial i = 32'hDEAD_BEEF;\n"
      "endmodule\n",
      "i");
  EXPECT_EQ(val, 0xDEADBEEFull);
}

TEST(NetAndVariableTypeSimulation, SigningSignedExtendsThroughArithmetic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [7:0] y;\n"
      "  initial begin\n"
      "    s = -4'sd3;\n"
      "    y = s;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val & 0xFFu, 0xFDu);
}

TEST(NetAndVariableTypeSimulation, NetTypeWireDrivesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [3:0] w;\n"
      "  assign w = 4'hA;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(NetAndVariableTypeSimulation, StructUnionPackedMemberAccess) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "  logic [3:0] y;\n"
      "  initial begin\n"
      "    s = 8'hA5;\n"
      "    y = s.lo;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 0x5u);
}

TEST(NetAndVariableTypeSimulation, EnumNameValueResolvesAtRuntime) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef enum logic [2:0] { A = 0, B = 1, C = 4 } e_t;\n"
      "  e_t e;\n"
      "  logic [2:0] y;\n"
      "  initial begin\n"
      "    e = C;\n"
      "    y = e;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 4u);
}

TEST(NetAndVariableTypeSimulation, PackedDimensionDrivesRuntimeWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter int W = 12;\n"
      "  logic [W-1:0] data;\n"
      "  initial data = '0;\n"
      "endmodule\n",
      f, "data");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 12u);
}

TEST(NetAndVariableTypeSimulation, IntegerVectorTypeBitIsTwoState) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [3:0] b;\n"
      "  initial b = 4'b1010;\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFu, 0xAu);
}

TEST(NetAndVariableTypeSimulation, VariableOfAUnitScopedTypeHasTheUnitsWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "typedef logic [3:0] T;\n"
      "module t;\n"
      "  typedef byte T;\n"
      "  $unit::T a;\n"
      "  initial a = 8'hAB;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(NetAndVariableTypeSimulation,
     NettypeRenamedThroughTheUnitScopeIsTheUnits) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("function automatic logic [3:0] ures(input logic [3:0] "
                 "d[]);\n"
                 "  ures = 4'hf;\n"
                 "  foreach (d[i]) ures = ures & d[i];\n"
                 "endfunction\n"
                 "nettype logic [3:0] nt with ures;\n"
                 "module t;\n"
                 "  function automatic logic [3:0] mres(input logic [3:0] "
                 "d[]);\n"
                 "    mres = 0;\n"
                 "    foreach (d[i]) mres = mres | d[i];\n"
                 "  endfunction\n"
                 "  nettype logic [3:0] nt with mres;\n"
                 "  nettype $unit::nt unt;\n"
                 "  unt n;\n"
                 "  assign n = 4'h3;\n"
                 "  assign n = 4'h5;\n"
                 "  initial begin\n"
                 "    #1;\n"
                 "    $display(\"%0h\", n);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1\n");
}

TEST(NetAndVariableTypeSimulation, VarClassPropertyOfImplicitTypeHasItsWidth) {
  auto val = RunAndGet(
      "class C;\n"
      "  var [7:0] z;\n"
      "endclass\n"
      "module t;\n"
      "  int out;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.z = 300;\n"
      "    out = c.z;\n"
      "  end\n"
      "endmodule\n",
      "out");
  EXPECT_EQ(val, 44u);
}

TEST(NetAndVariableTypeSimulation, TypeReferencesNameTheReferencedType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  logic [3:0] y;\n"
      "  typedef type(x) xt;\n"
      "  nettype type(y) nt;\n"
      "  xt v;\n"
      "  nt n;\n"
      "  struct packed { type(x) f; bit k; } s;\n"
      "  int r;\n"
      "  assign n = 4'hA;\n"
      "  initial begin\n"
      "    v = -5;\n"
      "    s.f = -5;\n"
      "    r = s.f;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"v", 0xFFFFFFFBu}, {"n", 0xAu}, {"r", 0xFFFFFFFBu}});
}

TEST(NetAndVariableTypeSimulation, PropertyAndFormalsOfATypeReference) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  var type(x) w;\n"
      "endclass\n"
      "module t;\n"
      "  int x;\n"
      "  int rw, ry, rz;\n"
      "  C c;\n"
      "  function automatic int f(input var type(x) y);\n"
      "    return y;\n"
      "  endfunction\n"
      "  function automatic int g;\n"
      "    input var type(x) z;\n"
      "    return z;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    c = new;\n"
      "    c.w = -5;\n"
      "    rw = c.w;\n"
      "    ry = f(-5);\n"
      "    rz = g(-5);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"rw", 0xFFFFFFFBu}, {"ry", 0xFFFFFFFBu}, {"rz", 0xFFFFFFFBu}});
}

TEST(NetAndVariableTypeSimulation,
     PropertyTypeReferencesFindAPropertyOrABuiltInType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "int g;\n"
      "class C;\n"
      "  function void touch();\n"
      "  endfunction\n"
      "  int x;\n"
      "  byte z;\n"
      "  var type(z) w;\n"
      "  var type(int) k;\n"
      "  var type(g) u;\n"
      "  var type(x + 1) e;\n"
      "endclass\n"
      "module t;\n"
      "  int rw, rk, ru;\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    c.w = -5;\n"
      "    c.k = -5;\n"
      "    c.u = -5;\n"
      "    rw = c.w;\n"
      "    rk = c.k;\n"
      "    ru = c.u;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"rw", 0xFFFFFFFBu}, {"rk", 0xFFFFFFFBu}, {"ru", 0xFFFFFFFBu}});
}

TEST(NetAndVariableTypeSimulation, DISABLED_AnEnumTakesItsTypeNameBasesWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  enum nib_t {A, B} e;\n"
      "  int w1, w2;\n"
      "  initial begin\n"
      "    w1 = $bits(A);\n"
      "    w2 = $bits(e);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"w1", 4u}, {"w2", 4u}});
}

TEST(NetAndVariableTypeSimulation, AnEnumTakesItsPackedTypeNameBasesWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic my_logic_t;\n"
      "  enum my_logic_t [3:0] {A, B, C} e;\n"
      "  int w;\n"
      "  initial w = $bits(e);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"w", 4u}});
}

TEST(NetAndVariableTypeSimulation, ANetTypeTakesAnExplicitDataType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module a(input wire logic [3:0] d, output int w);\n"
      "  assign w = $bits(d) + d;\n"
      "endmodule\n"
      "module b(d, w);\n"
      "  input wire logic [3:0] d;\n"
      "  output int w;\n"
      "  assign w = $bits(d) + d;\n"
      "endmodule\n"
      "module t;\n"
      "  int wa, wb;\n"
      "  a ua(5'h1F, wa);\n"
      "  b ub(5'h1F, wb);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"wa", 19u}, {"wb", 19u}});
}

TEST(NetAndVariableTypeSimulation, BitRegAndRealtimeCastTypes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int b0, b1, rz, r0, rt;\n"
      "  real q;\n"
      "  initial begin\n"
      "    b0 = bit'(1'bx);\n"
      "    b1 = bit'(4'b0011);\n"
      "    rz = (reg'(1'bz) === 1'bz);\n"
      "    r0 = reg'(4'b0010);\n"
      "    q = realtime'(7) / 2;\n"
      "    rt = q * 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design, {{"b0", 0u}, {"b1", 1u}, {"rz", 1u}, {"r0", 0u}, {"rt", 7u}});
}

TEST(NetAndVariableTypeSimulation,
     DISABLED_ACastToASpecializationsTypeParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class vector #(parameter width = 7, type T = int);\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  initial r = vector#(3, byte)::T'(300);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 44u}});
}

TEST(NetAndVariableTypeSimulation,
     DISABLED_ASizeCastByAGenerateBlockParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    localparam W = 3;\n"
      "  end\n"
      "  logic [7:0] r;\n"
      "  initial r = g[0].W'(8'hFF);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 7u}});
}

TEST(NetAndVariableTypeSimulation, DISABLED_ASizeCastByAnUnparenthesizedCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function int f(int a); return a; endfunction\n"
      "  logic [7:0] x = 8'hFF;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = $clog2(16)'(x);\n"
      "    b = f(3)'(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0xFu}, {"b", 7u}});
}

TEST(NetAndVariableTypeSimulation, ASizeCastByAGenvar) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x = 4'hF;\n"
      "  logic [3:0] y[1:3];\n"
      "  int s;\n"
      "  for (genvar i = 1; i < 4; i++) begin : g\n"
      "    assign y[i] = i'(x);\n"
      "  end\n"
      "  initial #1 s = y[1] + 10 * y[2] + 100 * y[3];\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"s", 731u}});
}

TEST(NetAndVariableTypeSimulation,
     DISABLED_ATypeOperandOpeningWithAClassScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class K; localparam int P = 2; endclass\n"
      "module t;\n"
      "  localparam int L = $bits(type(K::P + 1));\n"
      "  int r;\n"
      "  initial r = L;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 32u}});
}

TEST(NetAndVariableTypeSimulation, AClassScopedTypedefTakesPackedDimensions) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; typedef bit [4:0] t; endclass\n"
      "module t;\n"
      "  C::t [1:0] v;\n"
      "  int w, w1;\n"
      "  initial begin\n"
      "    w = $bits(v);\n"
      "    w1 = $bits(v[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"w", 10u}, {"w1", 5u}});
}

TEST(NetAndVariableTypeSimulation, ASignedTypedefOfAnIntegerVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic signed [3:0] st;\n"
      "  st v;\n"
      "  int r, w;\n"
      "  initial begin\n"
      "    v = 4'b1000;\n"
      "    r = v;\n"
      "    w = $bits(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 0xFFFFFFF8u}, {"w", 4u}});
}

TEST(NetAndVariableTypeSimulation, InlineAggregatesInAProgram) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  struct packed { logic [3:0] a; } s;\n"
      "  enum {P, Q} e;\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.a = 4'hA;\n"
      "    e = Q;\n"
      "    r = s.a * 10 + e;\n"
      "  end\n"
      "endprogram\n"
      "module t;\n"
      "  p u();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"u.r", 101u}});
}

TEST(NetAndVariableTypeSimulation, InlineAggregatesAsCheckerVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "checker ck;\n"
      "  struct packed { logic [3:0] a; } s;\n"
      "  enum {P, Q} e;\n"
      "  int bs;\n"
      "  always_comb bs = $bits(s) * 100 + $bits(e);\n"
      "endchecker\n"
      "module t;\n"
      "  ck c();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"c.bs", 432u}});
}

TEST(NetAndVariableTypeSimulation, InlineAggregatesInGenerateBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    struct packed { logic [3:0] a; } s;\n"
      "    enum {P, Q} e;\n"
      "  end\n"
      "  if (1) begin : h\n"
      "    struct packed { logic [3:0] a; } s;\n"
      "    enum {P, Q} e;\n"
      "  end\n"
      "  int r;\n"
      "  initial begin\n"
      "    g[1].s.a = 4'hA;\n"
      "    g[0].s.a = 4'h3;\n"
      "    h.s.a = 4'h5;\n"
      "    g[1].e = g[1].Q;\n"
      "    r = g[1].s.a * 1000 + g[0].s.a * 100 + h.s.a * 10 + g[1].e;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 10351u}});
}

TEST(NetAndVariableTypeSimulation, ANestedSpecializationTakesItsOwnParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Outer #(int A = 1);\n"
      "  class Inner #(int N = 2); bit [N-1:0] f; endclass\n"
      "endclass\n"
      "module t;\n"
      "  Outer#(8)::Inner#(4) h = new;\n"
      "  int w;\n"
      "  initial w = $bits(h.f);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"w", 4u}});
}

TEST(NetAndVariableTypeSimulation,
     DISABLED_AnExtendsChainReachesTheNestedClass) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A; class B; class C; int v = 7; endclass endclass endclass\n"
      "class B; class C; int v = 9; endclass endclass\n"
      "class H extends A::B::C; endclass\n"
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    H h = new;\n"
      "    r = h.v;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 7u}});
}

TEST(NetAndVariableTypeSimulation, DISABLED_AnExtendsThroughASpecializedScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Outer #(int A = 1);\n"
      "  class Inner; bit [A-1:0] g; endclass\n"
      "endclass\n"
      "class D extends Outer#(8)::Inner; endclass\n"
      "module t;\n"
      "  int w;\n"
      "  initial begin\n"
      "    D d = new;\n"
      "    w = $bits(d.g);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"w", 8u}});
}

TEST(NetAndVariableTypeSimulation, AnIncompleteClassScopeNamesTheLaterType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef class C;\n"
      "module t;\n"
      "  typedef C::T ct;\n"
      "  ct u;\n"
      "  var type(C::T) v;\n"
      "  localparam type P = C::T;\n"
      "  P x;\n"
      "  int r;\n"
      "  initial r = $bits(u) * 100 + $bits(v) * 10 + $bits(x);\n"
      "endmodule\n"
      "class C; typedef bit [4:0] T; endclass\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 555u}});
}

TEST(NetAndVariableTypeSimulation, AnIncompleteScopeChainNamesTheNestedType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef class C;\n"
      "class D; typedef bit [6:0] T; endclass\n"
      "module t;\n"
      "  typedef C::D::T ct;\n"
      "  ct v;\n"
      "  localparam type P = C::D::T;\n"
      "  P x;\n"
      "  int r;\n"
      "  initial r = $bits(v) * 10 + $bits(x);\n"
      "endmodule\n"
      "class C; class D; typedef bit [2:0] T; endclass endclass\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 33u}});
}

TEST(NetAndVariableTypeSimulation,
     DISABLED_AnIncompleteScopeChainInATypeReference) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef class C;\n"
      "class D; typedef bit [6:0] T; endclass\n"
      "module t;\n"
      "  var type(C::D::T) w;\n"
      "  int r;\n"
      "  initial r = $bits(w);\n"
      "endmodule\n"
      "class C; class D; typedef bit [2:0] T; endclass endclass\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 3u}});
}

TEST(NetAndVariableTypeSimulation,
     DISABLED_AnIncompleteScopeEndingInASpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef class C;\n"
      "module t;\n"
      "  typedef C::D#(4) dt;\n"
      "  int r;\n"
      "  initial begin\n"
      "    dt h = new;\n"
      "    r = $bits(h.f);\n"
      "  end\n"
      "endmodule\n"
      "class C; class D #(int W = 1); bit [W-1:0] f; endclass endclass\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 4u}});
}

}  // namespace
