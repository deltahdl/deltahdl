#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <format>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EnumerationSimulation, DefaultIntBaseTypeWidthAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  enum {IDLE, BUSY, DONE} state;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    state = BUSY;\n"
      "    observed = state;\n"
      "  end\n"
      "endmodule\n",
      f, "state");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
}

TEST(EnumerationSimulation, AutoIncrementedValuesPropagateAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  typedef enum {ZERO, ONE, TWO} count_t;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    observed = TWO;\n"
      "  end\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(EnumerationSimulation, ParameterSeededEnumValuePropagatesAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  parameter int BASE = 10;\n"
      "  enum integer {A = BASE, B} e;\n"
      "  int observed;\n"
      "  initial observed = B;\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(EnumerationSimulation, BareEnumDeclarationNamesConstantsAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  enum {red, yellow, green} light1;\n"
      "  int observed;\n"
      "  initial observed = green;\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(EnumerationSimulation, SharedEnumDeclaresItsConstantsOnce) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  enum {red, yellow, green} light1, light2;\n"
      "  int observed;\n"
      "  initial observed = yellow;\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EnumerationSimulation, StructMemberEnumLiteralOfAPackageReadsAtRuntime) {
  EXPECT_EQ(
      RunAndGet("package p;\n"
                "  typedef struct { enum {IDLE, BUSY} st; int n; } s_t;\n"
                "endpackage\n"
                "module top;\n"
                "  import p::*;\n"
                "  int observed;\n"
                "  initial observed = p::BUSY * 100 + BUSY * 10 + p::IDLE;\n"
                "endmodule\n",
                "observed"),
      110u);
}

TEST(EnumerationSimulation, StructMemberEnumLiteralOfAModuleReadsAtRuntime) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { enum {A, B} e; int n; } t;\n"
                      "  int observed;\n"
                      "  initial observed = B * 10 + A;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

TEST(EnumerationSimulation, PackageBareEnumLiteralReadsThroughAWildcardImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  enum {X, Y} v;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int observed;\n"
                      "  initial observed = Y * 10 + X;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

TEST(EnumerationSimulation, UnitScopeBareEnumLiteralReadsAtRuntime) {
  EXPECT_EQ(RunAndGet("enum {X, Y} v;\n"
                      "module top;\n"
                      "  int observed;\n"
                      "  initial observed = Y * 10 + X;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

TEST(EnumerationSimulation,
     UnitScopeTypedefEnumLiteralReadsBesideABareDeclaration) {
  EXPECT_EQ(RunAndGet("typedef enum {P, Q} t;\n"
                      "enum {X, Y} v;\n"
                      "module top;\n"
                      "  int observed;\n"
                      "  initial observed = Q * 10 + P;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

TEST(EnumerationSimulation, NegativeMemberOfAnIntBaseEnumPrintsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef enum int {A = 'h10, B = 32'b1_1, C = -8'sd6} e_t;\n"
      "  initial $display(\"A=%0d B=%0d C=%0d\", A, B, C);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "A=16 B=3 C=-6\n");
}

TEST(EnumerationSimulation, NegativeMemberOfAnEnumWithNoBasePrintsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  enum {N = -1, P} e;\n"
      "  initial $display(\"N=%0d P=%0d\", N, P);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "N=-1 P=0\n");
}

TEST(EnumerationSimulation, VariableOfAnIntBaseEnumPrintsItsMemberSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef enum int {A = 'h10, C = -8'sd6} e_t;\n"
      "  e_t v = C;\n"
      "  initial $display(\"v=%0d\", v);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "v=-6\n");
}

TEST(EnumerationSimulation, MemberOfALogicBaseEnumPrintsUnsigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef enum logic [3:0] {U = 4'hF} e_t;\n"
      "  initial $display(\"U=%0d\", U);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "U=15\n");
}

TEST(EnumerationSimulation, InlineEnumVariableTakesItsInitializer) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  var enum bit { clear, error } s1 = error;\n"
      "  enum bit { c2, e2 } s2 = e2;\n"
      "  var enum { a3, b3, c3 } s3 = c3;\n"
      "  typedef enum bit {x4, y4} t4;\n"
      "  var t4 s4 = y4;\n"
      "  initial $display(\"%s %s %s %s %0d %0d\", s1.name(), s2.name(),\n"
      "                   s3.name(), s4.name(), s1, s3);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "error e2 c3 y4 1 2\n");
}

TEST(EnumerationSimulation, EachDeclaratorOfAnInlineEnumTakesItsInitializer) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  enum {a, b, c} u = c, w = b;\n"
      "  initial $display(\"%s %s %0d %0d\", u.name(), w.name(), u, w);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "c b 2 1\n");
}

TEST(EnumerationSimulation, XOrZMemberOfA4StateEnumHoldsItsValue) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  enum integer {IDLE, XX='x, S1='b01, S2='b10} state;\n"
      "  enum logic [1:0] {A, Z='z, B=2} lz;\n"
      "  initial begin\n"
      "    state = XX; lz = Z;\n"
      "    $display(\"%0d %0d %0d %0d %0d %b %b\", $isunknown(XX), XX === 'x,\n"
      "             state === 'x, S1, S2, Z, lz);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1 2 zz zz\n");
}

TEST(EnumerationSimulation, BlockTypedefEnumHasItsMembersAndVariables) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    typedef enum {p, q} e_t;\n"
      "    e_t z;\n"
      "    z = z.last();\n"
      "    $display(\"[%s] %0d %0d %0d\", z.name(), z, z.num(), q);\n"
      "  end\n"
      "  task automatic tk;\n"
      "    typedef enum {a1, b1} f_t;\n"
      "    int j;\n"
      "    j = b1;\n"
      "    $display(\"%0d\", j);\n"
      "  endtask\n"
      "  initial #1 tk();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[q] 1 2 1\n1\n");
}

TEST(EnumerationSimulation, BlockTypedefEnumsOfTheSameNameKeepApart) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  parameter int K = 5;\n"
      "  function automatic int fn();\n"
      "    typedef enum {m0 = K, m1} h_t;\n"
      "    h_t hv;\n"
      "    hv = m1;\n"
      "    return hv + hv.num();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    typedef enum bit [1:0] {p = 1, q = 3} e_t;\n"
      "    e_t z;\n"
      "    z = q;\n"
      "    $display(\"A %s %0d %0d %0d\", z.name(), z, $bits(z), z.num());\n"
      "  end\n"
      "  initial #1 begin\n"
      "    typedef enum {p, q, r} e_t;\n"
      "    e_t z;\n"
      "    z = r;\n"
      "    $display(\"B %s %0d %0d %0d\", z.name(), z, z.num(), fn());\n"
      "  end\n"
      "  initial #2 fork\n"
      "    begin\n"
      "      typedef enum {V[2], w} g_t;\n"
      "      g_t g;\n"
      "      g = V1;\n"
      "      $display(\"C %s %0d %0d\", g.name(), g, w);\n"
      "    end\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "A q 3 2 2\nB r 2 3 8\nC V1 1 2\n");
}

TEST(EnumerationSimulation, BlockInlineEnumVariableHasItsMembers) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  task tk;\n"
      "    enum {p, q} z;\n"
      "    z = q;\n"
      "    $display(\"%s %0d\", z.name(), z);\n"
      "  endtask\n"
      "  initial begin\n"
      "    automatic enum {r, s} y = s;\n"
      "    $display(\"%s %0d\", y.name(), r);\n"
      "    tk();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s 0\nq 1\n");
}

TEST(EnumerationSimulation, XMemberOfAnEnumArrayIsNamedAtItsBaseWidth) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  enum logic [1:0] {A, X = 'x} [1:0] v;\n"
      "  typedef enum logic [1:0] {P, Y = 'x} [1:0] e_t;\n"
      "  typedef enum logic [1:0] {R, Z = 'x} [2:0] f_t;\n"
      "  f_t q;\n"
      "  typedef enum logic [1:0] {G, W = 'x} g_t;\n"
      "  g_t [1:0] s;\n"
      "  initial begin\n"
      "    $display(\"[%s] [%s] [%s] [%s] %b\", X.name(), Y.name(), Z.name(),\n"
      "             W.name(), Y);\n"
      "    $display(\"%0d %0d %0d\", $bits(v), $bits(q), $bits(s));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[X] [Y] [Z] [W] xx\n4 6 4\n");
}

TEST(EnumerationSimulation, BlockEnumArrayConstantsAreAsWideAsItsBase) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    typedef enum bit [1:0] {A, B, C} [1:0] e_t;\n"
      "    e_t x;\n"
      "    enum logic [2:0] {P, Q} [1:0] w;\n"
      "    enum logic [2:0] {R, S} y;\n"
      "    $display(\"%b %b %0d %0d %0d\", C, Q, $bits(x), $bits(w),\n"
      "             $bits(y));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "10 001 4 6 3\n");
}

TEST(EnumerationSimulation, PackageEnumArrayConstantsAreAsWideAsItsBase) {
  SimFixture f;
  auto out = RunCapture(
      "package pk;\n"
      "  enum bit [1:0] {A, B} [2:0] v;\n"
      "  typedef enum logic [2:0] {P, Q} [1:0] e_t;\n"
      "endpackage\n"
      "module t;\n"
      "  initial $display(\"%b %b\", pk::B, pk::Q);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "01 001\n");
}

struct EnumBase {
  const char* base;
  uint32_t width;
};

constexpr std::array kEnumBases = {
    EnumBase{"", 32},
    EnumBase{"byte", 8},
    EnumBase{"byte unsigned", 8},
    EnumBase{"shortint", 16},
    EnumBase{"int", 32},
    EnumBase{"int unsigned", 32},
    EnumBase{"longint", 64},
    EnumBase{"integer", 32},
    EnumBase{"time", 64},
    EnumBase{"bit", 1},
    EnumBase{"logic", 1},
    EnumBase{"reg unsigned", 1},
    EnumBase{"bit [11:0]", 12},
    EnumBase{"logic signed [2:0]", 3},
};

std::string EnumWidthDesign(const EnumBase& enum_base) {
  return std::format(
      "package p;\n"
      "  typedef enum {0} {{PA, PB}} e_t;\n"
      "endpackage\n"
      "typedef enum {0} {{UA, UB}} u_t;\n"
      "module t;\n"
      "  typedef enum {0} {{MA, MB}} m_t;\n"
      "  m_t mv;\n"
      "  enum {0} {{IA, IB}} iv;\n"
      "  p::e_t pv;\n"
      "  u_t uv;\n"
      "  typedef struct packed {{ m_t f; bit g; }} s_t;\n"
      "  localparam int kWidth = $bits(m_t);\n"
      "  bit [11:0] r;\n"
      "  if (1) begin : gb\n"
      "    typedef enum {0} {{GA, GB}} g_t;\n"
      "    g_t gv;\n"
      "    initial r[11] = $bits(gv) == {1} && $bits(g_t) == {1};\n"
      "  end\n"
      "  function automatic int local_width();\n"
      "    enum {0} {{FA, FB}} fv;\n"
      "    return $bits(fv);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    enum {0} {{LA, LB}} lv;\n"
      "    r[0] = $bits(mv) == {1};\n"
      "    r[1] = $bits(iv) == {1};\n"
      "    r[2] = $bits(pv) == {1};\n"
      "    r[3] = $bits(uv) == {1};\n"
      "    r[4] = $bits(m_t) == {1};\n"
      "    r[5] = $bits(p::e_t) == {1};\n"
      "    r[6] = $bits(u_t) == {1};\n"
      "    r[7] = $bits(s_t) == {1} + 1;\n"
      "    r[8] = kWidth == {1};\n"
      "    r[9] = $bits(lv) == {1};\n"
      "    r[10] = local_width() == {1};\n"
      "  end\n"
      "endmodule\n",
      enum_base.base, enum_base.width);
}

TEST(EnumerationSimulation, EnumerationIsAsWideAsItsBaseTypeEverywhere) {
  for (const EnumBase& enum_base : kEnumBases) {
    const std::string kSrc = EnumWidthDesign(enum_base);
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, "r"), 0xFFFu);
  }
}

std::string EnumWidthInOtherScopes(const EnumBase& enum_base) {
  const std::string kDeclared = std::format(
      "  typedef enum {0} {{XA, XB}} x_t;\n  x_t v;\n"
      "  enum {0} {{YA, YB}} w;\n",
      enum_base.base);
  const std::string kOk =
      std::format("$bits(v) == {0} && $bits(x_t) == {0} && $bits(w) == {0}",
                  enum_base.width);
  return std::format(
      "interface ifc;\n{0}  bit ok;\n  initial ok = {1};\nendinterface\n"
      "program pg;\n{0}  bit ok;\n"
      "  initial begin\n    ok = {1};\n    #2;\n  end\nendprogram\n"
      "checker ck;\n{0}  bit ok;\n  always_comb ok = {1};\nendchecker\n"
      "class c;\n{0}endclass\n"
      "module t;\n"
      "  ifc u_ifc();\n"
      "  pg u_pg();\n"
      "  ck u_ck();\n"
      "  bit ok;\n"
      "  c h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    ok = $bits(h.v) == {2} && $bits(c::x_t) == {2} &&\n"
      "         $bits(h.w) == {2};\n"
      "  end\n"
      "endmodule\n",
      kDeclared, kOk, enum_base.width);
}

TEST(EnumerationSimulation, EnumerationIsAsWideAsItsBaseInEveryScope) {
  for (const EnumBase& enum_base : kEnumBases) {
    const std::string kSrc = EnumWidthInOtherScopes(enum_base);
    SCOPED_TRACE(kSrc);
    for (const char* ok : {"u_ifc.ok", "u_pg.ok", "u_ck.ok", "ok"}) {
      SCOPED_TRACE(ok);
      EXPECT_EQ(RunAndGet(kSrc, ok), 1u);
    }
  }
}

TEST(EnumerationSimulation, EnumerationVariableHoldsItsBaseTypesBits) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef enum byte {A, B} sb_t;\n"
                      "  typedef enum byte unsigned {C, D} ub_t;\n"
                      "  typedef enum shortint {E, F} ss_t;\n"
                      "  typedef enum bit {G, H} b1_t;\n"
                      "  sb_t sb;\n"
                      "  ub_t ub;\n"
                      "  ss_t ss;\n"
                      "  b1_t b1;\n"
                      "  bit [3:0] r;\n"
                      "  initial begin\n"
                      "    sb = sb_t'(9'h1FF);\n"
                      "    ub = ub_t'(9'h1FF);\n"
                      "    ss = ss_t'(17'h1FFFF);\n"
                      "    b1 = b1_t'(2'b11);\n"
                      "    r[0] = int'(sb) == -1;\n"
                      "    r[1] = int'(ub) == 255;\n"
                      "    r[2] = int'(ss) == -1;\n"
                      "    r[3] = int'(b1) == 1;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xFu);
}

TEST(EnumerationSimulation, PackedArrayOfEnumerationsMultipliesItsBaseWidth) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef enum byte {A, B} [1:0] pb_t;\n"
                      "  typedef enum bit [5:0] {C, D} [2:0] pv_t;\n"
                      "  pb_t pb;\n"
                      "  pv_t pv;\n"
                      "  bit [3:0] r;\n"
                      "  initial begin\n"
                      "    r[0] = $bits(pb) == 16;\n"
                      "    r[1] = $bits(pb_t) == 16;\n"
                      "    r[2] = $bits(pv) == 18;\n"
                      "    r[3] = $bits(pv_t) == 18;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xFu);
}

TEST(EnumerationSimulation, ConstantOfAnEnumerationCarriesItsBasesSigning) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum byte {PM = -1, PN = 1} e_t;\n"
                      "  typedef enum byte unsigned {PU = 255} u_t;\n"
                      "endpackage\n"
                      "class c;\n"
                      "  typedef enum byte {CM = -1, CN = 1} e_t;\n"
                      "  typedef enum byte unsigned {CU = 255} u_t;\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef enum byte {MM = -1, MN = 1} e_t;\n"
                      "  typedef enum byte unsigned {MU = 255} u_t;\n"
                      "  int x;\n"
                      "  bit [5:0] r;\n"
                      "  initial begin\n"
                      "    x = MM;\n"
                      "    r[0] = x == -1;\n"
                      "    x = MU;\n"
                      "    r[1] = x == 255;\n"
                      "    x = p::PM;\n"
                      "    r[2] = x == -1;\n"
                      "    x = p::PU;\n"
                      "    r[3] = x == 255;\n"
                      "    x = c::CM;\n"
                      "    r[4] = x == -1;\n"
                      "    x = c::CU;\n"
                      "    r[5] = x == 255;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0x3Fu);
}

TEST(EnumerationSimulation, EnumerationMethodsReturnValuesOfItsBase) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef enum byte {M = -1, N = 1} e_t;\n"
                      "  typedef enum byte unsigned {U = 255, V = 1} u_t;\n"
                      "  e_t e;\n"
                      "  e_t e2 = N;\n"
                      "  u_t u;\n"
                      "  int x;\n"
                      "  bit [15:0] c;\n"
                      "  bit [5:0] r;\n"
                      "  initial begin\n"
                      "    e = M;\n"
                      "    u = U;\n"
                      "    r[0] = e == e.first();\n"
                      "    r[1] = e.next() == N;\n"
                      "    r[2] = e2.prev() == M;\n"
                      "    x = e.first();\n"
                      "    r[3] = x == -1;\n"
                      "    x = u.first();\n"
                      "    r[4] = x == 255;\n"
                      "    c = {e.first(), e.last()};\n"
                      "    r[5] = c == 16'hFF01;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0x3Fu);
}

}  // namespace
