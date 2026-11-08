#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ClassConstructorSim, ClauseExamplePropertiesAfterConstruction) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int c1 = 1;\n"
                      "  int c2 = 1;\n"
                      "  int c3 = 1;\n"
                      "  function new(int a);\n"
                      "    c2 = 2;\n"
                      "    c3 = a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  int d1 = 4;\n"
                      "  int d2 = c2;\n"
                      "  int d3 = 6;\n"
                      "  function new;\n"
                      "    super.new(d3);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D obj;\n"
                      "    obj = new;\n"
                      "    result = obj.c1 * 10000 + obj.c2 * 1000 +\n"
                      "             obj.d1 * 100 + obj.d2 * 10 + obj.d3;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            12426u);
}

TEST(ClassConstructorSim, LeadingSuperNewIsTheOneBaseConstructorCall) {
  EXPECT_EQ(RunAndGet("class base;\n"
                      "  static int ordinary = 0;\n"
                      "  string nm;\n"
                      "  bit is_root = 0;\n"
                      "  function new(string name, base parent);\n"
                      "    nm = name;\n"
                      "    if (parent == null && name == \"__top__\")\n"
                      "      is_root = 1;\n"
                      "    else\n"
                      "      ordinary = ordinary + 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class root extends base;\n"
                      "  function new();\n"
                      "    super.new(\"__top__\", null);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    root r;\n"
                      "    r = new;\n"
                      "    result = r.is_root * 100 + base::ordinary * 10 +\n"
                      "             (r.nm == \"__top__\");\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            101u);
}

TEST(ClassConstructorSim, DerivedBodyRunsAfterItsPropertiesAreInitialized) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int b = 1;\n"
                      "  function new(int v);\n"
                      "    b = v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int d = b;\n"
                      "  int y;\n"
                      "  function new(int v);\n"
                      "    super.new(v);\n"
                      "    y = d;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived obj;\n"
                      "    obj = new(9);\n"
                      "    result = obj.y * 10 + obj.d;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(ClassConstructorSim, ObjectConstructedInsideAConstructorBodyChainsOnce) {
  EXPECT_EQ(
      RunAndGet("class InnerBase;\n"
                "  static int runs = 0;\n"
                "  int v;\n"
                "  function new(int a);\n"
                "    runs = runs + 1;\n"
                "    v = a;\n"
                "  endfunction\n"
                "endclass\n"
                "class Inner extends InnerBase;\n"
                "  function new();\n"
                "    super.new(3);\n"
                "  endfunction\n"
                "endclass\n"
                "class OuterBase;\n"
                "  int w;\n"
                "  function new(int a);\n"
                "    w = a;\n"
                "  endfunction\n"
                "endclass\n"
                "class Outer extends OuterBase;\n"
                "  Inner child;\n"
                "  function new();\n"
                "    super.new(5);\n"
                "    child = new;\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    Outer o;\n"
                "    o = new;\n"
                "    result = o.w * 100 + InnerBase::runs * 10 + o.child.v;\n"
                "  end\n"
                "endmodule\n",
                "result"),
      513u);
}

TEST(ClassConstructorSim, LocalDeclarationAheadOfLeadingSuperNew) {
  EXPECT_EQ(RunAndGet("class base;\n"
                      "  int is_root;\n"
                      "  function new(string name, base parent);\n"
                      "    if (parent == null && name == \"__top__\") "
                      "is_root = 7;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class root extends base;\n"
                      "  int seen;\n"
                      "  extern function new();\n"
                      "endclass\n"
                      "function root::new();\n"
                      "  int scratch;\n"
                      "  super.new(\"__top__\", null);\n"
                      "  scratch = 3;\n"
                      "  seen = scratch;\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    root r;\n"
                      "    r = new;\n"
                      "    result = r.is_root * 10 + r.seen;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            73u);
}

TEST(ClassConstructorSim, ClassTypedPropertyNewInitializerConstructsItsObject) {
  EXPECT_EQ(RunAndGet("class baseA;\n"
                      "  int j = 5;\n"
                      "endclass\n"
                      "class B;\n"
                      "  int i = 1;\n"
                      "  baseA a = new;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    B b1;\n"
                      "    b1 = new;\n"
                      "    result = b1.a.j * 10 + b1.i;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            51u);
}

TEST(ClassConstructorSim, ClassTypedPropertyNewInitializerBindsItsArguments) {
  EXPECT_EQ(RunAndGet("class baseA;\n"
                      "  int j = 5;\n"
                      "  function new(int v);\n"
                      "    j = j + v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class B;\n"
                      "  baseA a = new(7);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    B b1;\n"
                      "    b1 = new;\n"
                      "    result = b1.a.j;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            12u);
}

TEST(ClassConstructorSim,
     ShallowCopySharesTheObjectAPropertyInitializerConstructed) {
  EXPECT_EQ(
      RunAndGet("class baseA;\n"
                "  int j = 5;\n"
                "endclass\n"
                "class B;\n"
                "  int i = 1;\n"
                "  baseA a = new;\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    B b1, b2;\n"
                "    b1 = new;\n"
                "    b2 = new b1;\n"
                "    b2.i = 10;\n"
                "    b2.a.j = 50;\n"
                "    result = b1.a.j * 100 + b1.i * 10 + (b1.a == b2.a);\n"
                "  end\n"
                "endmodule\n",
                "result"),
      5011u);
}

TEST(ClassConstructorSim, OutputFormalOfNewIsCopiedOutToTheCallersVariable) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static local int m_id = 3;\n"
                      "  int id;\n"
                      "  function new(output int oid);\n"
                      "    oid = m_id;\n"
                      "    id = m_id;\n"
                      "    m_id++;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int ia;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base a;\n"
                      "    a = new(ia);\n"
                      "    result = ia * 10 + a.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            33u);
}

TEST(ClassConstructorSim, OutputFormalOfNewIsCopiedOutOnEachConstruction) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static local int m_id = 0;\n"
                      "  int id;\n"
                      "  function new(output int oid);\n"
                      "    oid = m_id;\n"
                      "    id = m_id;\n"
                      "    m_id++;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int ia, ib;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base a, b;\n"
                      "    a = new(ia);\n"
                      "    b = new(ib);\n"
                      "    result = ia * 1000 + ib * 100 + a.id * 10 + b.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            101u);
}

TEST(ClassConstructorSim,
     OutputFormalOfNewIsCopiedOutThroughASubclassSuperNewCall) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static local int m_id = 5;\n"
                      "  int id;\n"
                      "  function new(output int oid);\n"
                      "    oid = m_id;\n"
                      "    id = m_id;\n"
                      "    m_id++;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D extends Base;\n"
                      "  function new(output int oid);\n"
                      "    super.new(oid);\n"
                      "    oid = oid + 100;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int ic;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D c;\n"
                      "    c = new(ic);\n"
                      "    result = ic * 10 + c.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1055u);
}

TEST(ClassConstructorSim,
     OutputFormalOfNewIsCopiedOutThroughASubclassDefaultArgument) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static local int m_id = 0;\n"
                      "  int id;\n"
                      "  function new(output int oid);\n"
                      "    oid = m_id;\n"
                      "    id = m_id;\n"
                      "    m_id++;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class A extends Base;\n"
                      "  function new(default);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int ia, ib, ic;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base a, b;\n"
                      "    A c;\n"
                      "    a = new(ia);\n"
                      "    b = new(ib);\n"
                      "    c = new(ic);\n"
                      "    result = ic * 10 + c.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            22u);
}

TEST(ClassConstructorSim, NewIntoAnInstancesHandleByItsPath) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class C; int v = 3; endclass\n"
                      "endpackage\n"
                      "module c; import p::*; C h; endmodule\n"
                      "module t;\n"
                      "  c u();\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    u.h = new;\n"
                      "    r = (u.h == null) ? 99 : u.h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            3u);
}

TEST(ClassConstructorSim, NewIntoANamedBlocksHandleByItsPath) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  class C; int v = 6; endclass\n"
                      "  int r;\n"
                      "  initial inner.h = new;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    begin : inner\n"
                      "      C h;\n"
                      "      r = (h == null) ? 99 : h.v;\n"
                      "    end\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            6u);
}

TEST(ClassConstructorSim, NewIntoAStructuresClassMember) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v;\n"
                      "  function new(int a); v = a; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef struct { int i; C h; } in_t;\n"
                      "  typedef struct { byte b; in_t n; C k; } st;\n"
                      "  st s;\n"
                      "  struct { int j; C m; } u;\n"
                      "  C x, y, z;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    s.k = new(3);\n"
                      "    s.n.h = new(5);\n"
                      "    u.m = new(7);\n"
                      "    x = s.k;\n"
                      "    y = s.n.h;\n"
                      "    z = u.m;\n"
                      "    r = (x == null || y == null || z == null)\n"
                      "        ? 0 : x.v * 100 + y.v * 10 + z.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            357u);
}

TEST(ClassConstructorSim, PropertyReadThroughAStructuresClassMember) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v;\n"
                      "  function new(int a); v = a; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef struct { int i; C h; } in_t;\n"
                      "  typedef struct { byte b; in_t n; C k; } st;\n"
                      "  st s;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    s.k = new(3);\n"
                      "    s.n.h = new(5);\n"
                      "    r = s.k.v * 10 + s.n.h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            35u);
}

TEST(ClassConstructorSim, PropertyReadThroughANullStructureMemberLetsRunGoOn) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v;\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef struct { int i; C k; } st;\n"
                      "  st s;\n"
                      "  int x, r;\n"
                      "  initial begin\n"
                      "    x = s.k.v;\n"
                      "    r = 7;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            7u);
}

}  // namespace
