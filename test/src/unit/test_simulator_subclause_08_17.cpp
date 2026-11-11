#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ChainedConstructorSimulation, SuperNewWithArgsInitializesBase) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(int v); x = v; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function new(int v); super.new(v); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Derived d = new(42);\n"
                      "    result = d.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ChainedConstructorSimulation, ImplicitSuperNewInitializesBase) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 7; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Derived d = new;\n"
                      "    result = d.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(ChainedConstructorSimulation, ThreeLevelChainingEndToEnd) {
  EXPECT_EQ(RunAndGet("class A;\n"
                      "  int a_val;\n"
                      "  function new(); a_val = 1; endfunction\n"
                      "endclass\n"
                      "class B extends A;\n"
                      "  int b_val;\n"
                      "  function new(); super.new(); b_val = 2; endfunction\n"
                      "endclass\n"
                      "class C extends B;\n"
                      "  int c_val;\n"
                      "  function new(); super.new(); c_val = 3; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    result = c.a_val + c.b_val * 10 + c.c_val * 100;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            321u);
}

TEST(ChainedConstructorSimulation, BaseConstructorRunsBeforeDerived) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 10; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y;\n"
                      "  function new();\n"
                      "    super.new();\n"
                      "    y = x + 5;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Derived d = new;\n"
                      "    result = d.y;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(ChainedConstructorSimulation, ImplicitSuperNewWithDerivedConstructor) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 100; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y;\n"
                      "  function new(); y = 200; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Derived d = new;\n"
                      "    result = d.x + d.y;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            300u);
}

TEST(ChainedConstructorSimulation, PropertyDefaultsInitializedDuringChaining) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x = 50;\n"
                      "  function new(); endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y = 25;\n"
                      "  function new(); super.new(); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Derived d = new;\n"
                      "    result = d.x + d.y;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            75u);
}

TEST(ChainedConstructorSimulation, ExtendsDefaultForwardsToBaseConstructor) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base(default);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Der d = new(55);\n"
                      "    result = d.bx;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(ChainedConstructorSimulation, SuperNewDefaultForwardsExpandedArgs) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base;\n"
                      "  int sz;\n"
                      "  function new(int sz, default);\n"
                      "    super.new(default);\n"
                      "    this.sz = sz;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Der d = new(7, 42);\n"
                      "    result = d.bx + d.sz * 100;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            742u);
}

TEST(ChainedConstructorSimulation,
     ImplicitSuperNewDefaultForwardsExpandedArgs) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base;\n"
                      "  int sz;\n"
                      "  function new(int sz, default);\n"
                      "    this.sz = sz;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Der d = new(3, 99);\n"
                      "    result = d.bx + d.sz * 100;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            399u);
}

TEST(ChainedConstructorSimulation, ExtendsDefaultWithUserConstructorForwards) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base(default);\n"
                      "  int sz;\n"
                      "  function new(int sz, default);\n"
                      "    this.sz = sz;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Der d = new(4, 88);\n"
                      "    result = d.bx + d.sz * 100;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            488u);
}

TEST(ChainedConstructorSimulation, DefaultForwardsMultipleArgsInOrder) {
  EXPECT_EQ(
      RunAndGet("class Base;\n"
                "  int ba;\n"
                "  int bb;\n"
                "  function new(int a, int b); ba = a; bb = b; endfunction\n"
                "endclass\n"
                "class Der extends Base;\n"
                "  int sz;\n"
                "  function new(int sz, default);\n"
                "    super.new(default);\n"
                "    this.sz = sz;\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    static Der d = new(1, 30, 4);\n"
                "    result = d.ba + d.bb * 10 + d.sz * 100;\n"
                "  end\n"
                "endmodule\n",
                "result"),
      170u);
}

TEST(ChainedConstructorSimulation, ExtendsDefaultAppliesBaseArgDefault) {
  EXPECT_EQ(
      RunAndGet("class Base;\n"
                "  int bx;\n"
                "  function new(int a, int b = 30); bx = a + b; endfunction\n"
                "endclass\n"
                "class Der extends Base(default);\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    static Der d = new(7);\n"
                "    result = d.bx;\n"
                "  end\n"
                "endmodule\n",
                "result"),
      37u);
}

TEST(ChainedConstructorSimulation, ExtendsArgsForwardToBaseConstructor) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int v); bx = v; endfunction\n"
                      "endclass\n"
                      "class Der extends Base(5);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Der d = new;\n"
                      "    result = d.bx;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(ChainedConstructorSimulation, DefaultBeforeOwnArgForwards) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base;\n"
                      "  bit en;\n"
                      "  function new(default, bit enable);\n"
                      "    super.new(default);\n"
                      "    this.en = enable;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Der d = new(20, 1);\n"
                      "    result = d.bx + d.en * 1000;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1020u);
}

TEST(ChainedConstructorSimulation, SuperNewWithArgsRunsTheBaseConstructorOnce) {
  EXPECT_EQ(
      RunAndGet("class Base;\n"
                "  static int runs = 0;\n"
                "  static int first = 0;\n"
                "  int x;\n"
                "  function new(int v);\n"
                "    runs = runs + 1;\n"
                "    if (runs == 1) first = v;\n"
                "    x = v;\n"
                "  endfunction\n"
                "endclass\n"
                "class Derived extends Base;\n"
                "  function new();\n"
                "    super.new(5);\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    Derived d;\n"
                "    d = new;\n"
                "    result = Base::runs * 100 + Base::first * 10 + d.x;\n"
                "  end\n"
                "endmodule\n",
                "result"),
      155u);
}

TEST(ChainedConstructorSimulation, SuperNewFormalsReachEachLevelOnce) {
  EXPECT_EQ(RunAndGet("class A;\n"
                      "  static int a_runs = 0;\n"
                      "  int a_val;\n"
                      "  function new(int v);\n"
                      "    a_runs = a_runs + 1;\n"
                      "    a_val = v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class B extends A;\n"
                      "  static int b_runs = 0;\n"
                      "  int b_val;\n"
                      "  function new(int v);\n"
                      "    super.new(v + 1);\n"
                      "    b_runs = b_runs + 1;\n"
                      "    b_val = v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class C extends B;\n"
                      "  function new(int v);\n"
                      "    super.new(v + 1);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new(1);\n"
                      "    result = A::a_runs * 1000 + B::b_runs * 100 +\n"
                      "             c.a_val * 10 + c.b_val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1132u);
}

TEST(ChainedConstructorSimulation, DefaultExpandsEachDirectionAndType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  local static int m_id;\n"
      "  string name;\n"
      "  function new(string name, output int id);\n"
      "    this.name = name;\n"
      "    id = m_id++;\n"
      "  endfunction\n"
      "endclass\n"
      "class A extends Base; function new(default); endfunction endclass\n"
      "class B extends Base;\n"
      "  int size;\n"
      "  function new(int size, default);\n"
      "    super.new(default);\n"
      "    this.size = size;\n"
      "  endfunction\n"
      "endclass\n"
      "class A2 extends Base(default); endclass\n"
      "class BI;\n"
      "  int got;\n"
      "  function new(inout int v); got = v; v = v + 100; endfunction\n"
      "endclass\n"
      "class DI extends BI; function new(default); endfunction endclass\n"
      "class BR; function new(ref int v); v = 9; endfunction endclass\n"
      "class DR extends BR; function new(default); endfunction endclass\n"
      "class BY; int got; function new(byte v); got = v; endfunction "
      "endclass\n"
      "class DY extends BY; function new(default); endfunction endclass\n"
      "module m;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8;\n"
      "  initial begin\n"
      "    automatic int k, k2, iv, rv;\n"
      "    automatic A a; automatic B b; automatic A2 a2;\n"
      "    automatic DI di; automatic DR dr; automatic DY dy;\n"
      "    a = new(\"x\", k); r1 = k + 10 * (a.name == \"x\");\n"
      "    a = new(\"x\", k); r2 = k;\n"
      "    b = new(4, \"y\", k);\n"
      "    r3 = k * 100 + b.size * 10 + (b.name == \"y\");\n"
      "    a2 = new(\"w\", k); r4 = k + 10 * (a2.name == \"w\");\n"
      "    iv = 5; di = new(iv); r5 = di.got * 1000 + iv;\n"
      "    rv = 1; dr = new(rv); r6 = rv;\n"
      "    dy = new(300); r7 = dy.got;\n"
      "    a = new(.name(\"n\"), .id(k2)); r8 = k2 * 10 + (a.name == \"n\");\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 10u},
                    {"r2", 1u},
                    {"r3", 241u},
                    {"r4", 13u},
                    {"r5", 5105u},
                    {"r6", 9u},
                    {"r7", 44u},
                    {"r8", 41u}});
}

TEST(ChainedConstructorSimulation,
     DISABLED_DefaultExpandsAListThatItselfHoldsDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  local static int m_id;\n"
      "  string name;\n"
      "  function new(string name, output int id);\n"
      "    this.name = name;\n"
      "    id = m_id++;\n"
      "  endfunction\n"
      "endclass\n"
      "class B extends Base;\n"
      "  int size;\n"
      "  function new(int size, default);\n"
      "    super.new(default);\n"
      "    this.size = size;\n"
      "  endfunction\n"
      "endclass\n"
      "class C extends B;\n"
      "  bit enable;\n"
      "  function new(default, bit enable);\n"
      "    super.new(default);\n"
      "    this.enable = enable;\n"
      "  endfunction\n"
      "endclass\n"
      "class IB; int bx; function new(int nv); bx = nv; endfunction "
      "endclass\n"
      "class IM extends IB;\n"
      "  int size;\n"
      "  function new(int size, default); this.size = size; endfunction\n"
      "endclass\n"
      "class IC extends IM;\n"
      "  int en;\n"
      "  function new(default, int enable); en = enable; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    automatic int k;\n"
      "    automatic C c; automatic IC ic;\n"
      "    c = new(4, \"z\", k, 1);\n"
      "    r1 = c.size * 100 + (c.name == \"z\") * 10 + c.enable;\n"
      "    c = new(4, \"z\", k, 1); r2 = k;\n"
      "    ic = new(4, 5, 6); r3 = ic.size * 100 + ic.bx * 10 + ic.en;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 411u}, {"r2", 1u}, {"r3", 456u}});
}

TEST(ChainedConstructorSimulation,
     DISABLED_ExpandedArgumentsAreReadByNameInTheBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class CQ; int bx; function new(int x = 1); bx = x; endfunction "
      "endclass\n"
      "class F1 extends CQ;\n"
      "  int k;\n"
      "  function new(default, int y); super.new(default); k = x + y; "
      "endfunction\n"
      "endclass\n"
      "class F2 extends CQ; int k; function new(default); k = x * 10; "
      "endfunction endclass\n"
      "class F3 extends CQ(default);\n"
      "  int k;\n"
      "  function new(int y, default); k = x * 10 + y; endfunction\n"
      "endclass\n"
      "class E3 extends CQ; int k; extern function new(default, int y); "
      "endclass\n"
      "function E3::new(default, int y); super.new(default); k = x + y; "
      "endfunction\n"
      "module m;\n"
      "  int r1, r2, r3, r4;\n"
      "  initial begin\n"
      "    automatic F1 f1 = new(2, 5); automatic F2 f2 = new(4);\n"
      "    automatic F3 f3 = new(1, 3); automatic E3 e3 = new(2, 6);\n"
      "    r1 = f1.k; r2 = f2.k + f2.bx; r3 = f3.k; r4 = e3.k;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 7u}, {"r2", 44u}, {"r3", 31u}, {"r4", 8u}});
}

TEST(ChainedConstructorSimulation,
     ArgumentsAfterDefaultAreInputLogicByDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base; int bx; function new(int nv); bx = nv; endfunction "
      "endclass\n"
      "class D1 extends Base;\n"
      "  logic e1; logic f1;\n"
      "  function new(default, en, fn); e1 = en; f1 = fn; endfunction\n"
      "endclass\n"
      "class D2 extends Base;\n"
      "  function new(default, output int oa, ob); oa = 11; ob = 12; "
      "endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int r1, r2, r3, r4;\n"
      "  initial begin\n"
      "    automatic D1 a; automatic D1 b; automatic D2 c; automatic int p, "
      "q;\n"
      "    a = new(1, 2, 3); r1 = a.e1 * 10 + a.f1; r4 = a.bx;\n"
      "    b = new(1, 'x, 1'bz);\n"
      "    r2 = (b.e1 === 1'bx) * 10 + (b.f1 === 1'bz);\n"
      "    c = new(1, p, q); r3 = p * 100 + q;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u}, {"r2", 11u}, {"r3", 1112u}, {"r4", 1u}});
}

TEST(ChainedConstructorSimulation, ConstructorsRunFromTheRootDownAtEveryLevel) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  static int order;\n"
      "  int bx;\n"
      "  function new(int nv); bx = nv; order = order * 10 + 1; "
      "endfunction\n"
      "endclass\n"
      "class D1 extends Base;\n"
      "  function new(default); order = order * 10 + 2; endfunction\n"
      "endclass\n"
      "class D3 extends Base(5);\n"
      "  int y;\n"
      "  function new(); y = bx + 1; order = order * 10 + 3; endfunction\n"
      "endclass\n"
      "class D4 extends D3; endclass\n"
      "class D5 extends D4;\n"
      "  function new(); order = order * 10 + 5; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    automatic D1 a; automatic D5 d;\n"
      "    Base::order = 0; a = new(8); r1 = Base::order * 10 + a.bx;\n"
      "    Base::order = 0; d = new; r2 = Base::order;\n"
      "    r3 = d.bx * 10 + d.y;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 128u}, {"r2", 135u}, {"r3", 56u}});
}

TEST(ChainedConstructorSimulation,
     VirtualMethodCalledFromABaseConstructorReachesTheOverride) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class B;\n"
      "  int seen;\n"
      "  int nv;\n"
      "  function new(); seen = probe(); nv = plain(); endfunction\n"
      "  virtual function int probe(); return 1; endfunction\n"
      "  function int plain(); return 1; endfunction\n"
      "endclass\n"
      "class D extends B;\n"
      "  int k = 7;\n"
      "  int after;\n"
      "  function new(); super.new(); after = probe(); endfunction\n"
      "  virtual function int probe(); return 100 + k; endfunction\n"
      "  function int plain(); return 2; endfunction\n"
      "endclass\n"
      "class E extends D;\n"
      "  int j = 5;\n"
      "  virtual function int probe(); return 200 + j; endfunction\n"
      "endclass\n"
      "class D2 extends B;\n"
      "  int k = 7;\n"
      "  virtual function int probe(); return 300 + k; endfunction\n"
      "endclass\n"
      "class BT;\n"
      "  int seen;\n"
      "  function new(); run(); endfunction\n"
      "  virtual task run(); seen = 1; endtask\n"
      "endclass\n"
      "class DT extends BT;\n"
      "  int k = 7;\n"
      "  virtual task run(); seen = 100 + k; endtask\n"
      "endclass\n"
      "module m;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8;\n"
      "  initial begin\n"
      "    automatic D d = new; automatic B b = new; automatic E e = new;\n"
      "    automatic D2 d2 = new; automatic DT dt = new;\n"
      "    r1 = d.seen; r2 = d.after; r3 = d.nv; r4 = b.seen;\n"
      "    r5 = e.seen; r6 = e.after; r7 = d2.seen; r8 = dt.seen;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 100u},
                    {"r2", 107u},
                    {"r3", 1u},
                    {"r4", 1u},
                    {"r5", 200u},
                    {"r6", 200u},
                    {"r7", 300u},
                    {"r8", 100u}});
}

TEST(ChainedConstructorSimulation,
     DISABLED_OverrideRunFromABaseConstructorSeesLogicPropertiesAsX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class BL;\n"
      "  logic [3:0] got;\n"
      "  function new(); got = probe(); endfunction\n"
      "  virtual function logic [3:0] probe(); return 1; endfunction\n"
      "endclass\n"
      "class DL extends BL;\n"
      "  logic [3:0] k = 7;\n"
      "  virtual function logic [3:0] probe(); return k; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    automatic DL dl = new;\n"
      "    r1 = (dl.got === 4'bxxxx); r2 = (dl.k === 4'd7);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 1u}});
}

}  // namespace
