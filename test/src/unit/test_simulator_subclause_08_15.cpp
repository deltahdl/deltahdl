#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(SuperSimulation, SuperPropertyReturnsBaseValue) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int value;\n"
                      "  function new(); value = 10; endfunction\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "  int value;\n"
                      "  function new(); super.new(); value = 20; endfunction\n"
                      "  function int get_base_value();\n"
                      "    return super.value;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static LinkedPacket lp = new;\n"
                      "    result = lp.get_base_value();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

TEST(SuperSimulation, SuperMethodCallDispatchesToBase) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int value;\n"
                      "  function new(); value = 3; endfunction\n"
                      "  function int delay();\n"
                      "    return value * value;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "  int value;\n"
                      "  function new(); super.new(); value = 5; endfunction\n"
                      "  function int delay();\n"
                      "    return super.delay() + value * super.value;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static LinkedPacket lp = new;\n"
                      "    result = lp.delay();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            24u);
}

TEST(SuperSimulation, SuperAccessesInheritedMember) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 99; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function new(); super.new(); endfunction\n"
                      "  function int get();\n"
                      "    return super.x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Derived d = new;\n"
                      "    result = d.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(SuperSimulation, SuperPropertyWriteUpdatesBase) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 1; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int x;\n"
                      "  function new(); super.new(); x = 2; endfunction\n"
                      "  function void set_base(int v);\n"
                      "    super.x = v;\n"
                      "  endfunction\n"
                      "  function int get_base();\n"
                      "    return super.x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Derived d = new;\n"
                      "    d.set_base(55);\n"
                      "    result = d.get_base();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(SuperSimulation, SuperReachesInheritedGrandparentMember) {
  EXPECT_EQ(RunAndGet("class A;\n"
                      "  int x;\n"
                      "  function new(); x = 10; endfunction\n"
                      "endclass\n"
                      "class B extends A;\n"
                      "  function new(); super.new(); endfunction\n"
                      "endclass\n"
                      "class C extends B;\n"
                      "  function new(); super.new(); endfunction\n"
                      "  function int get();\n"
                      "    return super.x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    result = c.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

TEST(SuperSimulation, SuperInitializationOrder) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 5; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y;\n"
                      "  function new();\n"
                      "    super.new();\n"
                      "    y = super.x + 1;\n"
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
            6u);
}

TEST(SuperSimulation, ImplicitSuperNewInitializesBase) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 7; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y;\n"
                      "  function new(); y = 2; endfunction\n"
                      "  function int get_base();\n"
                      "    return super.x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Derived d = new;\n"
                      "    result = d.get_base();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(SuperSim, BaseConstructorWriteReadThroughHandleFromAnotherClass) {
  EXPECT_EQ(RunAndGet("class InnerBase;\n"
                      "  int v;\n"
                      "  function new(int a);\n"
                      "    v = a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Inner extends InnerBase;\n"
                      "  int k;\n"
                      "  function new();\n"
                      "    super.new(3);\n"
                      "    k = 9;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Plain;\n"
                      "  Inner child;\n"
                      "  int seen;\n"
                      "  function new();\n"
                      "    child = new;\n"
                      "    seen = child.v * 10 + child.k;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Plain p;\n"
                      "    p = new;\n"
                      "    result = p.seen * 100 + p.child.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3903u);
}

TEST(SuperSim, BaseWriteLeavesAShadowingDerivedPropertyAlone) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int v;\n"
                      "  function new(int a);\n"
                      "    v = a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Der extends Base;\n"
                      "  int v = 7;\n"
                      "  function new();\n"
                      "    super.new(3);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Der d;\n"
                      "    d = new;\n"
                      "    result = d.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(SuperSimulation, SuperNamesAnInheritedAssociativeProperty) {
  auto v = RunAndGet(
      "module t;\n"
      "  class Base;\n"
      "    int m[string];\n"
      "  endclass\n"
      "  class Sub extends Base;\n"
      "    function void fill(); m[\"a\"] = 9; super.m[\"b\"] = 4; "
      "endfunction\n"
      "    function int show(); return super.m.num() * 100 + super.m[\"a\"] * "
      "10\n"
      "      + m[\"b\"]; endfunction\n"
      "  endclass\n"
      "  Sub s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = new; s.fill();\n"
      "    result = s.show();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 294u);
}

TEST(SuperSimulation, SuperReachesAHiddenBaseAssociativeProperty) {
  auto v = RunAndGet(
      "module t;\n"
      "  class Base;\n"
      "    int m[string];\n"
      "    function int base_num(); return m.num(); endfunction\n"
      "  endclass\n"
      "  class Sub extends Base;\n"
      "    int m[string];\n"
      "    function void fill(); m[\"a\"] = 9; super.m[\"b\"] = 1;\n"
      "      super.m[\"c\"] = 2; endfunction\n"
      "    function int show(); return super.m.num() * 100 + m.num() * 10\n"
      "      + super.m[\"c\"]; endfunction\n"
      "  endclass\n"
      "  Sub s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = new; s.fill();\n"
      "    result = s.show() * 10 + s.base_num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2122u);
}

TEST(SuperSim, VirtualInterfaceMemberReadThroughSuper) {
  auto v = RunAndGet(
      "interface SBus; int a; endinterface\n"
      "class Base; virtual SBus vif; endclass\n"
      "class Derived extends Base;\n"
      "  function int sv(); return super.vif.a; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  SBus s();\n"
      "  Derived d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new; d.vif = s; s.a = 64;\n"
      "    result = d.sv();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 64u);
}

TEST(SuperSimulation, SuperReachesTheBaseMemberOfEveryKind) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A;\n"
      "  int x = 1;\n"
      "  static int s = 30;\n"
      "  virtual function int vf(); return 100; endfunction\n"
      "  function int g(); return 7; endfunction\n"
      "  task tk(output int o); o = 11; endtask\n"
      "  static function int sf(); return 40; endfunction\n"
      "endclass\n"
      "class B extends A;\n"
      "  int x = 2;\n"
      "  static int s = 31;\n"
      "  virtual function int vf(); return 200 + super.vf(); endfunction\n"
      "  task tk(output int o); int t; super.tk(t); o = t + 1000; endtask\n"
      "  static function int sf(); return 41; endfunction\n"
      "endclass\n"
      "class C extends B;\n"
      "  int x = 3;\n"
      "  virtual function int vf(); return 300 + super.vf(); endfunction\n"
      "  function int bx(); return super.x; endfunction\n"
      "  function int bs(); return super.s; endfunction\n"
      "  function int bg(); return super.g(); endfunction\n"
      "  function int bsf(); return super.sf(); endfunction\n"
      "  function int bt(); int o; super.tk(o); return o; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5, r6, r7;\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    automatic A a = c;\n"
      "    r1 = c.vf(); r2 = a.vf(); r3 = c.bx(); r4 = c.bs();\n"
      "    r5 = c.bg(); r6 = c.bsf(); r7 = c.bt();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 600u},
                    {"r2", 600u},
                    {"r3", 2u},
                    {"r4", 31u},
                    {"r5", 7u},
                    {"r6", 41u},
                    {"r7", 1011u}});
}

TEST(SuperSimulation, SuperStopsAtTheMemberOneLevelUp) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A;\n"
      "  int x = 1;\n"
      "  function int g(); return 5; endfunction\n"
      "endclass\n"
      "class B extends A;\n"
      "  int x = 2;\n"
      "  function int g(); return 6; endfunction\n"
      "endclass\n"
      "class C extends B;\n"
      "  int x = 3;\n"
      "  function int g(); return 8; endfunction\n"
      "  function int bx(); return super.x * 10 + super.g(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1;\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    r1 = c.bx();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 26u}});
}

TEST(SuperSimulation, SuperReachesTheBaseMemberInEveryPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  class P; int i = 1; function int get(); return 10; endfunction "
      "endclass\n"
      "  class L extends P; int i = 2; function int get(); "
      "return super.i + super.get(); endfunction endclass\n"
      "endpackage\n"
      "interface itf;\n"
      "  class IP; int i = 3; endclass\n"
      "  class IL extends IP; int i = 4; function int get(); "
      "return super.i; endfunction endclass\n"
      "  function automatic int t(); IL l = new; return l.get(); "
      "endfunction\n"
      "endinterface\n"
      "program pg(output int r);\n"
      "  class QP; int i = 5; endclass\n"
      "  class QL extends QP; int i = 6; function int get(); "
      "return super.i; endfunction endclass\n"
      "  initial begin automatic QL l = new; r = l.get(); end\n"
      "endprogram\n"
      "module t;\n"
      "  int r1, r2, r3, r4;\n"
      "  itf i();\n"
      "  pg p(r4);\n"
      "  if (1) begin : g\n"
      "    class GP; int i = 9; endclass\n"
      "    class GL extends GP; int i = 10; function int get(); "
      "return super.i; endfunction endclass\n"
      "    function automatic int t(); GL l = new; return l.get(); "
      "endfunction\n"
      "  end\n"
      "  initial begin\n"
      "    automatic pk::L l = new;\n"
      "    r1 = l.get(); r2 = i.t(); r3 = g.t();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 11u}, {"r2", 3u}, {"r3", 9u}, {"r4", 5u}});
}

TEST(SuperSimulation, DISABLED_SuperInANestedSiblingClassReachesTheBaseMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Out;\n"
      "  class NP; int i = 7; endclass\n"
      "  class NL extends NP; int i = 8; function int get(); "
      "return super.i; endfunction endclass\n"
      "  static function int t(); NL l = new; return l.get(); "
      "endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1;\n"
      "  initial r1 = Out::t();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 7u}});
}

TEST(SuperSimulation, SuperReadsTheBaseValueAndLocalParameters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class G #(int GG = 11); endclass\n"
      "class B #(int P = 3) extends G #(13);\n"
      "  localparam int L = P + 1;\n"
      "  parameter int Q = 7;\n"
      "endclass\n"
      "class D extends B #(5);\n"
      "  localparam int P = 9;\n"
      "  localparam int L = 0;\n"
      "  int r_tk, r_c1, r_c2;\n"
      "  function new(); super.new(); r_c1 = super.P; r_c2 = super.L; "
      "endfunction\n"
      "  function int sp(); return super.P * 100 + P; endfunction\n"
      "  function int sl(); return super.L * 100 + L; endfunction\n"
      "  function int sq(); return super.Q; endfunction\n"
      "  function int sg(); return super.GG; endfunction\n"
      "  task tk(); r_tk = super.P; endtask\n"
      "endclass\n"
      "class E extends B;\n"
      "  int r_c;\n"
      "  function new(); r_c = super.P * 2; endfunction\n"
      "  function int sp(); return super.P; endfunction\n"
      "endclass\n"
      "class F #(int N = 2) extends B #(N * 2);\n"
      "  function int sp(); return super.P; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11;\n"
      "  initial begin\n"
      "    automatic D d = new;\n"
      "    automatic E e = new;\n"
      "    automatic F f = new;\n"
      "    automatic F #(4) f4 = new;\n"
      "    d.tk();\n"
      "    r1 = d.sp(); r2 = d.sl(); r3 = d.sq(); r4 = d.sg();\n"
      "    r5 = d.r_tk; r6 = d.r_c1; r7 = d.r_c2; r8 = e.sp();\n"
      "    r9 = f.sp(); r10 = f4.sp(); r11 = e.r_c;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 509u},
                    {"r2", 600u},
                    {"r3", 7u},
                    {"r4", 13u},
                    {"r5", 5u},
                    {"r6", 5u},
                    {"r7", 6u},
                    {"r8", 3u},
                    {"r9", 4u},
                    {"r10", 8u},
                    {"r11", 6u}});
}

TEST(SuperSimulation, ImplicitSuperNewRunsTheBaseConstructorFirstAtEveryLevel) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A;\n"
      "  static int log;\n"
      "  int x;\n"
      "  function new(); log = log * 10 + 4; x = 7; endfunction\n"
      "endclass\n"
      "class B extends A;\n"
      "endclass\n"
      "class C extends B;\n"
      "  function new(); log = log * 10 + 3; endfunction\n"
      "endclass\n"
      "class E extends A;\n"
      "  function new(); log = log * 10 + 9; endfunction\n"
      "endclass\n"
      "class F extends A;\n"
      "  int y = 2;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5;\n"
      "  initial begin\n"
      "    automatic C c;\n"
      "    automatic B b;\n"
      "    automatic E e;\n"
      "    automatic F f;\n"
      "    c = new; r1 = A::log; A::log = 0;\n"
      "    b = new; r2 = A::log; A::log = 0;\n"
      "    e = new; r3 = A::log;\n"
      "    f = new; r4 = f.x; r5 = e.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 43u}, {"r2", 4u}, {"r3", 49u}, {"r4", 7u}, {"r5", 7u}});
}

TEST(SuperSimulation,
     DISABLED_ImplicitSuperNewCallsABaseConstructorWithDefaultArguments) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A;\n"
      "  static int log;\n"
      "  function new(int k = 4); log = log * 10 + k; endfunction\n"
      "endclass\n"
      "class B extends A;\n"
      "endclass\n"
      "class C extends B;\n"
      "  function new(); log = log * 10 + 3; endfunction\n"
      "endclass\n"
      "class D extends A;\n"
      "  function new(); super.new(); log = log * 10 + 3; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    automatic B b;\n"
      "    automatic C c;\n"
      "    automatic D d;\n"
      "    b = new; r1 = A::log; A::log = 0;\n"
      "    c = new; r2 = A::log; A::log = 0;\n"
      "    d = new; r3 = A::log;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 4u}, {"r2", 43u}, {"r3", 43u}});
}

}  // namespace
