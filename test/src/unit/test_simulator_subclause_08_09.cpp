#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StaticClassPropertySim, SharedAcrossInstancesViaHandle) {
  EXPECT_EQ(RunAndGet("class Counter;\n"
                      "  static int count;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Counter a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.count = 7;\n"
                      "    result = b.count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(StaticClassPropertySim, WriteThenReadBackViaSameHandle) {
  EXPECT_EQ(RunAndGet("class Counter;\n"
                      "  static int count;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Counter a;\n"
                      "    a = new;\n"
                      "    a.count = 21;\n"
                      "    result = a.count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            21u);
}

TEST(StaticClassPropertySim, InitializedOnceSurvivesReconstruction) {
  EXPECT_EQ(RunAndGet("class Counter;\n"
                      "  static int count = 5;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Counter a;\n"
                      "    a = new;\n"
                      "    a.count = 20;\n"
                      "    a = new;\n"
                      "    result = a.count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

TEST(StaticClassPropertySim, InitializerValueReadWithoutObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int base = 42;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C::base;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(StaticClassPropertySim, ZeroInitializedReadWithoutObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int s;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = 100 + C::s;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            100u);
}

TEST(StaticClassPropertySim, WriteAndReadWithoutObjectViaScope) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::x = 99;\n"
                      "    result = C::x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(StaticClassPropertySim, ScopeWriteVisibleViaHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int s;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a;\n"
                      "    a = new;\n"
                      "    C::s = 33;\n"
                      "    result = a.s;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            33u);
}

TEST(StaticClassPropertySim, HandleWriteVisibleViaScope) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int s;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a;\n"
                      "    a = new;\n"
                      "    a.s = 44;\n"
                      "    result = C::s;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            44u);
}

TEST(StaticClassPropertySim, InstancePropertyNotShared) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.v = 7;\n"
                      "    result = b.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(StaticClassPropertySim, SharedPackedVectorAcrossInstances) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static bit [7:0] count;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.count = 8'hAB;\n"
                      "    result = b.count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0xABu);
}

TEST(StaticClassPropertySim, SharedStringAcrossInstances) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static string name;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.name = \"hello\";\n"
                      "    result = (b.name == \"hello\") ? 100 : 0;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            100u);
}

TEST(StaticClassPropertySim, SharedRealAcrossInstances) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("class C;\n"
                                 "  static real r;\n"
                                 "endclass\n"
                                 "module t;\n"
                                 "  real out;\n"
                                 "  initial begin\n"
                                 "    C a, b;\n"
                                 "    a = new;\n"
                                 "    b = new;\n"
                                 "    a.r = 3.5;\n"
                                 "    out = b.r;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "out"),
                   3.5);
}

TEST(StaticClassPropertySim, VectorInitializerReadWithoutObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static bit [7:0] x = 8'hFF;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C::x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0xFFu);
}

TEST(StaticClassPropertySim, StaticQueuePropertyPushedFromConstructors) {
  EXPECT_EQ(RunAndGet("class Reg;\n"
                      "  static Reg all[$];\n"
                      "  int id;\n"
                      "  function new(int i);\n"
                      "    id = i;\n"
                      "    all.push_back(this);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static Reg a = new(3);\n"
                      "    static Reg b = new(5);\n"
                      "    out = Reg::all.size() * 10 + Reg::all[1].id;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            25u);
}

TEST(StaticClassPropertySim, StaticPropertyThroughAPackageQualifiedClassScope) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  class Cfg;\n"
                      "    static int depth = 3;\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import pk::Cfg;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = pk::Cfg::depth * 10 + Cfg::depth;\n"
                      "    pk::Cfg::depth = 7;\n"
                      "    result = result * 100 + Cfg::depth;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3307u);
}

TEST(StaticClassPropertySim, StaticPropertyThroughAPackageQualifiedScopeAlone) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  class Cfg;\n"
                      "    static int depth = 3;\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = pk::Cfg::depth + 40;\n"
                      "endmodule\n",
                      "result"),
            43u);
}

TEST(StaticClassPropertySim, ModuleStaticInitializerReadsTheModulesVariable) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int K = 3;\n"
                      "  class C;\n"
                      "    static int s = K;\n"
                      "  endclass\n"
                      "  int result;\n"
                      "  initial result = C::s;\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(StaticClassPropertySim, ModuleStaticMailboxBoundByTheModulesVariable) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  int K = 1;\n"
                "  class C;\n"
                "    static mailbox mb = new(K);\n"
                "  endclass\n"
                "  int result;\n"
                "  initial result = C::mb.try_put(1) * 10 + C::mb.try_put(2);\n"
                "endmodule\n",
                "result"),
      10u);
}

TEST(StaticClassPropertySim, PropertyReadThroughTheClassScopedStaticHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  static C m_inst;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    C::m_inst = c;\n"
                      "    result = (C::m_inst == null) * 100 + C::m_inst.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            9u);
}

TEST(StaticClassPropertySim, PropertyWrittenThroughTheClassScopedStaticHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  C kid;\n"
                      "  static C m_inst;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.kid = new;\n"
                      "    C::m_inst = c;\n"
                      "    C::m_inst.k = 4;\n"
                      "    result = c.k * 10 + C::m_inst.kid.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            49u);
}

TEST(StaticClassPropertySim, StaticMethodReadsAPropertyThroughItsStaticHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  static C m_inst;\n"
                      "  static function int k_via_static();\n"
                      "    if (m_inst == null) m_inst = new;\n"
                      "    return m_inst.k;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C::k_via_static();\n"
                      "endmodule\n",
                      "result"),
            9u);
}

TEST(StaticClassPropertySim, StaticMethodCallsAndWritesThroughItsStaticHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  static C m_inst;\n"
                      "  function void add(int v); k = k + v; endfunction\n"
                      "  static function int go();\n"
                      "    C c;\n"
                      "    if (m_inst == null) m_inst = new;\n"
                      "    m_inst.add(7);\n"
                      "    m_inst.k = m_inst.k + 20;\n"
                      "    c = m_inst;\n"
                      "    return c.k;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C::go();\n"
                      "endmodule\n",
                      "result"),
            36u);
}

TEST(StaticClassPropertySim, PackageClassStaticHandleReachesItsObject) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class C;\n"
                      "    int k = 9;\n"
                      "    static C m_inst;\n"
                      "    function void add(int v); k = k + v; endfunction\n"
                      "    static function int go();\n"
                      "      if (m_inst == null) begin\n"
                      "        m_inst = new;\n"
                      "        m_inst.add(7);\n"
                      "      end\n"
                      "      return m_inst.k;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C::go() * 100;\n"
                      "    result = result + p::C::m_inst.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1616u);
}

TEST(StaticClassPropertySim, StaticHandleDispatchesByItsDeclaredClass) {
  EXPECT_EQ(RunAndGet("class B;\n"
                      "  static B m_inst;\n"
                      "  function int who(); return 1; endfunction\n"
                      "  virtual function int tag(); return 10; endfunction\n"
                      "endclass\n"
                      "class D extends B;\n"
                      "  function int who(); return 2; endfunction\n"
                      "  virtual function int tag(); return 20; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D d;\n"
                      "    d = new;\n"
                      "    B::m_inst = d;\n"
                      "    result = B::m_inst.who() * 100 + B::m_inst.tag();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            120u);
}

TEST(StaticClassPropertySim, Uninitialized4StateStaticReadsX) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C;\n"
                 "    logic l;\n"
                 "    static logic sl; static logic [3:0] sv;\n"
                 "    static int sn;\n"
                 "  endclass\n"
                 "  C c;\n"
                 "  initial begin\n"
                 "    c = new;\n"
                 "    $display(\"l=%0h sl=%0h sv=%b sn=%0d hsl=%0h\", c.l,\n"
                 "             C::sl, C::sv, C::sn, c.sl);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "l=x sl=x sv=xxxx sn=0 hsl=x\n");
}

TEST(StaticClassPropertySim, NewAssignedToAStaticThroughAStaticHandle) {
  EXPECT_EQ(RunAndGet("class Q;\n"
                      "  int k = 3;\n"
                      "endclass\n"
                      "class C;\n"
                      "  static C m_t_inst;\n"
                      "  static Q m_tw;\n"
                      "  static function void init();\n"
                      "    m_t_inst = new;\n"
                      "    m_t_inst.m_tw = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::init();\n"
                      "    result = C::m_tw == null ? 7 : C::m_tw.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(StaticClassPropertySim, ValueAssignedToAStaticThroughAStaticHandle) {
  EXPECT_EQ(RunAndGet("class Q;\n"
                      "  int k = 3;\n"
                      "endclass\n"
                      "class C;\n"
                      "  static C m_t_inst;\n"
                      "  static Q m_tw;\n"
                      "  static function void init();\n"
                      "    Q q = new;\n"
                      "    q.k = 5;\n"
                      "    m_t_inst = new;\n"
                      "    m_t_inst.m_tw = q;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::init();\n"
                      "    result = C::m_tw == null ? 7 : C::m_tw.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(StaticClassPropertySim,
     StaticMethodCallsThroughItsStaticHandleUnderAnotherClassesMethod) {
  EXPECT_EQ(
      RunAndGet("class Q;\n"
                "  function int k(); return 4; endfunction\n"
                "endclass\n"
                "class C;\n"
                "  static Q m_t;\n"
                "  static function int via(); return m_t.k(); endfunction\n"
                "endclass\n"
                "class Other;\n"
                "  function int go();\n"
                "    C::m_t = new;\n"
                "    return C::via();\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    static Other o = new;\n"
                "    result = o.go();\n"
                "  end\n"
                "endmodule\n",
                "result"),
      4u);
}

TEST(StaticPropertySim, StaticHandleInitializedWithNewHoldsAnObject) {
  const std::string kSrc =
      "module t;\n"
      "  class C;\n"
      "    int ci;\n"
      "    static C inst = new;\n"
      "    function new(); ci = 5; endfunction\n"
      "  endclass\n"
      "  int hl, ci;\n"
      "  initial begin\n"
      "    hl = C::inst != null;\n"
      "    ci = C::inst.ci;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "hl"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "ci"), 5u);
}

TEST(StaticClassPropertySim, StaticArrayPropertiesAreShared) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    static int sarr[3];\n"
      "    static int sd[];\n"
      "    static function void init(); sarr[2] = 7; sd = new[3]; sd[1] = 5;\n"
      "    endfunction\n"
      "    function int get(); return sarr[2] * 10 + sd[1]; endfunction\n"
      "  endclass\n"
      "  C g, k;\n"
      "  initial begin\n"
      "    g = new; k = new;\n"
      "    C::init();\n"
      "    k.sarr[0] = 4;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", C::sarr[2], g.sarr[2],\n"
      "             k.get(), C::sd.size(), g.sd[1], g.sarr[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 7 75 3 5 4\n");
}

TEST(StaticClassPropertySim, StaticArrayPropertyTakesPatternInitializer) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  static int t[4] = '{1, 2, 3, 4};\n"
      "  static byte r[2:0] = '{7, 8, 9};\n"
      "  static int d[] = '{5, 6};\n"
      "  static function int sum();\n"
      "    int s;\n"
      "    s = 0;\n"
      "    foreach (t[i]) s += t[i];\n"
      "    return s;\n"
      "  endfunction\n"
      "  function int last(); return d[d.size() - 1]; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", C::t[2], C::sum(), C::r[2],\n"
      "             C::d.size(), c.last(), C::t[0] + C::r[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 10 7 2 6 10\n");
}

TEST(StaticClassPropertySim, StaticInitializerRunsOnceHoweverManyObjects) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int calls;\n"
      "  function int tick(); calls++; return calls; endfunction\n"
      "  class C; static int s = tick(); endclass\n"
      "  class D extends C; endclass\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C a, b, c;\n"
      "    D d, e;\n"
      "    a = new; b = new; c = new; d = new; e = new;\n"
      "    r1 = calls;\n"
      "    r2 = C::s;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 1u}});
}

TEST(StaticClassPropertySim, StaticInitializerRunsWithNoObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int calls;\n"
      "  function int tick(); calls++; return calls; endfunction\n"
      "  class C; static int s = tick(); endclass\n"
      "  int r1, r2;\n"
      "  initial #1 begin\n"
      "    r1 = calls;\n"
      "    r2 = C::s;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 1u}});
}

TEST(StaticClassPropertySim,
     EachStaticInitializerRunsOnceAndAnInstanceOnePerObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int calls;\n"
      "  function int tick(); calls++; return calls; endfunction\n"
      "  class C;\n"
      "    static int s = tick();\n"
      "    static int s2 = tick();\n"
      "    int n = tick();\n"
      "  endclass\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C a, b, c;\n"
      "    #1 r1 = calls;\n"
      "    a = new; b = new; c = new;\n"
      "    r2 = calls;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 2u}, {"r2", 5u}});
}

TEST(StaticClassPropertySim, EachSpecializationInitializesItsOwnStaticOnce) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  int calls;\n"
                "  function int tick(); calls++; return calls; endfunction\n"
                "  class P #(int W = 1);\n"
                "    static int s = tick() * 10 + W;\n"
                "  endclass\n"
                "  int r;\n"
                "  initial begin\n"
                "    P #(1) a, b;\n"
                "    P #(2) c;\n"
                "    a = new; b = new; c = new;\n"
                "    r = calls * 1000 + P#(1)::s % 10 * 100 +\n"
                "        P#(2)::s % 10 * 10 + (P#(1)::s / 10 != "
                "P#(2)::s / 10);\n"
                "  end\n"
                "endmodule\n",
                "r"),
      2121u);
}

TEST(StaticClassPropertySim,
     DISABLED_StaticPropertyThroughANullHandleIsTheSharedVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Packet; static int fileID = 7; int n; endclass\n"
      "class DP extends Packet; endclass\n"
      "class O; Packet p; endclass\n"
      "module t;\n"
      "  function int f(Packet q); return q.fileID; endfunction\n"
      "  int r1, r2, r3, r4, r5, r6, r7;\n"
      "  initial begin\n"
      "    Packet p, arr[2];\n"
      "    O o;\n"
      "    DP d;\n"
      "    r1 = p.fileID;\n"
      "    p.fileID = 9;\n"
      "    r2 = Packet::fileID;\n"
      "    p = new;\n"
      "    p = null;\n"
      "    p.fileID = 10;\n"
      "    r3 = p.fileID;\n"
      "    r4 = arr[1].fileID;\n"
      "    o = new;\n"
      "    r5 = o.p.fileID;\n"
      "    r6 = f(null);\n"
      "    r7 = d.fileID;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 7u},
                    {"r2", 9u},
                    {"r3", 10u},
                    {"r4", 10u},
                    {"r5", 10u},
                    {"r6", 10u},
                    {"r7", 10u}});
}

}  // namespace
