#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TypedConstructorCallSim, ConstructsSpecifiedType) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function new(); x = 1; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(); super.new(); x = 42; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = D::new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(TypedConstructorCallSim, TypedConstructorWithPositionalArgs) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int val;\n"
                      "  function new(int v); val = v; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(int v); super.new(v); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = D::new(99);\n"
                      "    result = c.val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(TypedConstructorCallSim, TypedConstructorWithNamedArgs) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int val;\n"
                      "  function new(int v); val = v; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = C::new(.v(55));\n"
                      "    result = c.val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(TypedConstructorCallSim, TypedConstructorSameType) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int val;\n"
                      "  function new(); val = 33; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = C::new;\n"
                      "    result = c.val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            33u);
}

TEST(TypedConstructorCallSim, TypedConstructorInitializesProperties) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a;\n"
      "  int b;\n"
      "  function new(int x, int y);\n"
      "    a = x;\n"
      "    b = y;\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  function new(int x, int y); super.new(x, y); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ra, rb;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = D::new(10, 20);\n"
      "    ra = c.a;\n"
      "    rb = c.b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 10u}, {"rb", 20u}});
}

TEST(TypedConstructorCallSim, TypedConstructorPropertyDefaults) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x = 5;\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  int y = 10;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = D::new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(TypedConstructorCallSim, ParameterizedTypedConstructor) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int val;\n"
                      "  function new(); val = 0; endfunction\n"
                      "endclass\n"
                      "class E #(int N = 1) extends C;\n"
                      "  function new(); super.new(); val = N; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = E#(.N(77))::new;\n"
                      "    result = c.val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            77u);
}

TEST(TypedConstructorCallSim, MultiLevelInheritanceConstructsSpecifiedType) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function new(); x = 1; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(); super.new(); x = 2; endfunction\n"
                      "endclass\n"
                      "class E extends D;\n"
                      "  function new(); super.new(); x = 3; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = E::new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(TypedConstructorCallSim, TypedConstructorAsBlockLocalDeclInit) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function new(); x = 1; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(); super.new(); x = 42; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static C c = D::new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(TypedConstructorCallSim, TypedConstructorAsStaticDeclInit) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function new(); x = 1; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(); super.new(); x = 42; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  C c = D::new;\n"
                      "  int result;\n"
                      "  initial result = c.x;\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(TypedConstructorCallSim, TypedConstructorAppliesDefaultArgument) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int a;\n"
                      "  int b;\n"
                      "  function new(int x, int y = 20);\n"
                      "    a = x;\n"
                      "    b = y;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = C::new(5);\n"
                      "    result = c.b;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

TEST(TypedConstructorCallSim, TypedConstructorWithTypeParameterSpecialization) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int val;\n"
                      "  function new(); val = 0; endfunction\n"
                      "endclass\n"
                      "class E #(type T = int) extends C;\n"
                      "  function new(T v); super.new(); val = v; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = E#(.T(byte))::new(.v(5));\n"
                      "    result = c.val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(TypedConstructorCallSim, ParameterizedTypedConstructorWithArgs) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int val;\n"
                      "  function new(); val = 0; endfunction\n"
                      "endclass\n"
                      "class E #(int N = 1) extends C;\n"
                      "  int extra;\n"
                      "  function new(int e); super.new(); val = N; extra = e; "
                      "endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = E#(.N(10))::new(.e(20));\n"
                      "    result = c.val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

TEST(TypedConstructorCallSim, TypedConstructorCallRunsInEachPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; int x = 1; endclass\n"
      "class D extends C;\n"
      "  function new(int v = 7); x = v; endfunction\n"
      "endclass\n"
      "class H;\n"
      "  C hc = D::new(3);\n"
      "  function C mk(); C c; c = D::new(4); return c; endfunction\n"
      "endclass\n"
      "package k;\n"
      "  class PC; int x; endclass\n"
      "  class PD extends PC; function new(); x = 11; endfunction endclass\n"
      "  function int pf(); PC c; c = PD::new; return c.x; endfunction\n"
      "endpackage\n"
      "function int uf(); C c; c = D::new(5); return c.x; endfunction\n"
      "interface ifc; C c = D::new(6); endinterface\n"
      "module t;\n"
      "  ifc i();\n"
      "  H h = new;\n"
      "  int r1, r2, r3, r4, r5, r6;\n"
      "  if (1) begin : g\n"
      "    C gc = D::new(9);\n"
      "  end\n"
      "  initial begin\n"
      "    automatic C m = h.mk();\n"
      "    r1 = h.hc.x;\n"
      "    r2 = m.x;\n"
      "    r3 = k::pf();\n"
      "    r4 = uf();\n"
      "    r5 = i.c.x;\n"
      "    r6 = g.gc.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 3u},
                    {"r2", 4u},
                    {"r3", 11u},
                    {"r4", 5u},
                    {"r5", 6u},
                    {"r6", 9u}});
}

TEST(TypedConstructorCallSim,
     DISABLED_TypedConstructorOfASpecializationConstructsThatSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class E #(type T = int);\n"
      "  T y;\n"
      "  function new(T v); y = v; endfunction\n"
      "  function int w(); return $bits(y); endfunction\n"
      "endclass\n"
      "class F #(int N = 4);\n"
      "  bit [N-1:0] y;\n"
      "  function new(int v); y = v; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  E #(byte) b, c;\n"
      "  F #(3) f1;\n"
      "  int r1, r2, r3, r4, r5;\n"
      "  initial begin\n"
      "    b = new(300);\n"
      "    c = E#(byte)::new(300);\n"
      "    f1 = F#(3)::new(13);\n"
      "    r1 = b.y;\n"
      "    r2 = c.y;\n"
      "    r3 = c.w();\n"
      "    r4 = f1.y;\n"
      "    c = E#(.T(byte))::new(.v(301));\n"
      "    r5 = c.y;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 44u}, {"r2", 44u}, {"r3", 8u}, {"r4", 5u}, {"r5", 45u}});
}

TEST(TypedConstructorCallSim,
     DISABLED_TypedConstructorWithoutParenthesesTakesTheDefaultArguments) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; int x = 1; endclass\n"
      "class D extends C;\n"
      "  int y = 3;\n"
      "  function new(int v = 7); x = v; endfunction\n"
      "endclass\n"
      "class H;\n"
      "  int x = 2;\n"
      "  function new(int v = 6); x = v; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C m = D::new;\n"
      "  int r1, r2, r3, r4, r5, r6;\n"
      "  initial begin\n"
      "    automatic C n = D::new;\n"
      "    automatic C n2 = D::new();\n"
      "    C a;\n"
      "    H h;\n"
      "    a = D::new;\n"
      "    h = H::new;\n"
      "    r1 = m.x;\n"
      "    r2 = n.x;\n"
      "    r3 = a.x;\n"
      "    r4 = h.x;\n"
      "    r5 = n2.x;\n"
      "    a = D::new();\n"
      "    r6 = a.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 7u}, {"r2", 7u}, {"r3", 7u}, {"r4", 6u}, {"r5", 7u}, {"r6", 7u}});
}

TEST(TypedConstructorCallSim,
     DISABLED_TypedConstructorIntoAnElementOrPropertyBuildsTheObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class BasePacket; virtual function int send(); return 5; endfunction "
      "endclass\n"
      "class TokenPacket extends BasePacket; function int send(); return 2; "
      "endfunction endclass\n"
      "class H; BasePacket p; endclass\n"
      "module m;\n"
      "  BasePacket packets[4];\n"
      "  BasePacket dq[$];\n"
      "  BasePacket b;\n"
      "  H h = new;\n"
      "  int r1, r2, r3, r4, r5;\n"
      "  initial begin\n"
      "    packets[2] = TokenPacket::new(); r1 = (packets[2] == null) ? 99 : "
      "packets[2].send();\n"
      "    packets[3] = new; r2 = (packets[3] == null) ? 99 : "
      "packets[3].send();\n"
      "    h.p = TokenPacket::new; r3 = (h.p == null) ? 99 : h.p.send();\n"
      "    dq = '{null}; dq[0] = TokenPacket::new; r4 = (dq[0] == null) ? 99 : "
      "dq[0].send();\n"
      "    b = TokenPacket::new; r5 = (b == null) ? 99 : b.send();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design, {{"r1", 2u}, {"r2", 5u}, {"r3", 2u}, {"r4", 2u}, {"r5", 2u}});
}

}  // namespace
