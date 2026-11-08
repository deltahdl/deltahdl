#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

namespace {

TEST(ObjectPropertySim,
     UnpackedStructPropertyMembersWrittenAndReadThroughAHandle) {
  EXPECT_EQ(RunAndGet("typedef struct { int f; int g; } pair_t;\n"
                      "class C;\n"
                      "  pair_t p;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.p.f = 3;\n"
                      "    c.p.g = 12;\n"
                      "    out = c.p.f * 100 + c.p.g;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            312u);
}

TEST(ObjectPropertySim, UnpackedStructPropertyMembersWrittenAndReadInMethods) {
  EXPECT_EQ(RunAndGet("typedef struct { int f; int g; } pair_t;\n"
                      "class C;\n"
                      "  pair_t p;\n"
                      "  function void setf(int x); p.f = x; endfunction\n"
                      "  function void setg(int x); p.g = x; endfunction\n"
                      "  function int sum(); return p.f * 100 + p.g; "
                      "endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.setf(7);\n"
                      "    c.setg(25);\n"
                      "    out = c.sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            725u);
}

TEST(ObjectPropertySim,
     UnpackedStructPropertyMemberWrittenThroughAHandleReadInAMethod) {
  EXPECT_EQ(RunAndGet("typedef struct { int f; int g; } pair_t;\n"
                      "class C;\n"
                      "  pair_t p;\n"
                      "  function int sum(); return p.f + p.g; endfunction\n"
                      "  function void setg(int x); p.g = x; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.p.f = 3;\n"
                      "    c.setg(12);\n"
                      "    out = c.p.f * 1000 + c.p.g * 10 + c.sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3135u);
}

TEST(ObjectPropertySim, PackageScopedEnumPropertyHoldsItsInitializer) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
                      "endpackage\n"
                      "class C;\n"
                      "  pk::sev_t s = pk::MED;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    out = c.s * 10;\n"
                      "    c.s = pk::HIGH;\n"
                      "    out = out + c.s;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            23u);
}

TEST(ObjectPropertySim, PackageScopedEnumReturnedByAMethod) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
                      "endpackage\n"
                      "class C;\n"
                      "  pk::sev_t s = pk::MED;\n"
                      "  function pk::sev_t cur(); return s; endfunction\n"
                      "  function pk::sev_t top();\n"
                      "    s = pk::HIGH;\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    out = c.cur() * 100;\n"
                      "    out = out + c.top() * 10;\n"
                      "    out = out + c.cur();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            233u);
}

TEST(ObjectPropertySim, ElementsOfAStructPropertysArrayMember) {
  const char* src =
      "module t;\n"
      "  typedef struct { int a; byte data[3]; } pkt_t;\n"
      "  class C;\n"
      "    pkt_t s;\n"
      "    function void fill(); s.data[2] = 9; s.data[0] = 4; endfunction\n"
      "    function int get(); return s.data[2]; endfunction\n"
      "    function int get_this(); return this.s.data[0]; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int d2, d0, d1, g, gt;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.fill();\n"
      "    h.s.data[1] = 7;\n"
      "    d2 = h.s.data[2];\n"
      "    d0 = h.s.data[0];\n"
      "    d1 = h.s.data[1];\n"
      "    g = h.get();\n"
      "    gt = h.get_this();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "d2"), 9u);
  EXPECT_EQ(RunAndGet(src, "d0"), 4u);
  EXPECT_EQ(RunAndGet(src, "d1"), 7u);
  EXPECT_EQ(RunAndGet(src, "g"), 9u);
  EXPECT_EQ(RunAndGet(src, "gt"), 4u);
}

TEST(ObjectPropertySim, DynamicArrayPropertyOfStructsInAMethod) {
  const char* src =
      "module t;\n"
      "  typedef struct { int a; int b; } s_t;\n"
      "  class C;\n"
      "    s_t d[];\n"
      "    function void fill(); d = new[2]; d[1].a = 11; endfunction\n"
      "  endclass\n"
      "  s_t d[];\n"
      "  C h;\n"
      "  int n, a1, md;\n"
      "  initial begin\n"
      "    d = new[3];\n"
      "    h = new;\n"
      "    h.fill();\n"
      "    n = h.d.size();\n"
      "    a1 = h.d[1].a;\n"
      "    md = d.size();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 2u);
  EXPECT_EQ(RunAndGet(src, "a1"), 11u);
  EXPECT_EQ(RunAndGet(src, "md"), 3u);
}

TEST(ObjectPropertySim, AssociativeArrayPropertyOfStructMemberWrites) {
  const char* src =
      "module t;\n"
      "  typedef struct { int x; int y; } pt_t;\n"
      "  class C;\n"
      "    pt_t m[string];\n"
      "    function void fill(); m[\"a\"].x = 3; m[\"a\"].y = 4; "
      "endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int ax, ay, bx, n;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.fill();\n"
      "    h.m[\"b\"].x = 9;\n"
      "    ax = h.m[\"a\"].x;\n"
      "    ay = h.m[\"a\"].y;\n"
      "    bx = h.m[\"b\"].x;\n"
      "    n = h.m.num();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ax"), 3u);
  EXPECT_EQ(RunAndGet(src, "ay"), 4u);
  EXPECT_EQ(RunAndGet(src, "bx"), 9u);
  EXPECT_EQ(RunAndGet(src, "n"), 2u);
}

TEST(ObjectPropertySim, PatternInitializerOfArrayPropertyFillsEachElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int f[4] = '{5, 1, 8, 3};\n"
      "  endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    result = h.f[0] * 1000 + h.f[1] * 100 + h.f[2] * 10 + h.f[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5183u);
}

TEST(ObjectPropertySim, PatternAssignedToArrayPropertyInAMethodIsStored) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int a[3];\n"
      "    function new(); a = '{1, 2, 3}; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    result = h.a[0] * 100 + h.a[1] * 10 + h.a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 123u);
}

TEST(ObjectPropertySim, KeyedAndReplicatedPatternsIntoArrayPropertyViaHandle) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C; int a[3]; int r[3]; endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.a = '{1:9, default:1};\n"
      "    h.r = '{3{3}};\n"
      "    result = (h.a[0] * 100 + h.a[1] * 10 + h.a[2]) * 10 + h.r[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1913u);
}

TEST(ObjectPropertySim, DefaultPatternIntoStructPropertyViaHandleFillsAll) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x; int y; } st;\n"
      "  class C; st s; endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.s = '{default:8};\n"
      "    result = h.s.x * 10 + h.s.y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 88u);
}

TEST(ObjectPropertySim, KeyedPatternIntoStructPropertyInAMethodFillsAll) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x; int y; } st;\n"
      "  class C;\n"
      "    st s;\n"
      "    function void f(); s = '{x:6, default:1}; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.f();\n"
      "    result = h.s.x * 10 + h.s.y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 61u);
}

TEST(ObjectPropertySim, WriteThroughChainedHandleIsTheObjectsProperty) {
  auto v = RunAndGet(
      "module t;\n"
      "  class Inner;\n"
      "    int k;\n"
      "    function int getk(); return k; endfunction\n"
      "  endclass\n"
      "  class Holder; Inner d; endclass\n"
      "  Holder h; Inner i;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new; h.d = new;\n"
      "    h.d.k = 64;\n"
      "    i = h.d;\n"
      "    result = h.d.getk() * 1000 + i.k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 64064u);
}

TEST(ObjectPropertySim, StringArrayPropertyElementsWrittenFromOutside) {
  auto v = RunAndGet(
      "class C;\n"
      "  string inst[2];\n"
      "  static string names[2];\n"
      "  string sd[];\n"
      "  function void set(); inst[0] = \"in\"; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new; h.set();\n"
      "    h.inst[1] = \"ab\"; C::names[0] = \"s\";\n"
      "    h.sd = new[1]; h.sd[0] = \"dy\";\n"
      "    result = (h.inst[0] == \"in\") + 10 * (h.inst[1] == \"ab\") +\n"
      "             100 * (C::names[0] == \"s\") + 1000 * (h.sd[0] == \"dy\") "
      "+\n"
      "             10000 * h.inst[1].len();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 21111u);
}

TEST(ObjectPropertySim, StructurePropertyPrintsAsPatternWithP) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; int b; } GS;\n"
                       "class Box;\n"
                       "  GS s;\n"
                       "  function void set(); s.b = 5; s.a = 3; endfunction\n"
                       "  function void show(); $display(\"m=%p\", s); "
                       "endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box b;\n"
                       "  initial begin\n"
                       "    b = new; b.set(); b.show();\n"
                       "    $display(\"h=%p\", b.s);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "m='{a:3, b:5}\nh='{a:3, b:5}\n");
}

constexpr const char* kOptBox =
    "typedef union tagged { void None; int Some; } Opt;\n"
    "class Box;\n"
    "  Opt o;\n"
    "  function void set(int v); o = tagged Some (v); endfunction\n"
    "  function void clear(); o = tagged None; endfunction\n"
    "  function string describe();\n"
    "    case (o) matches\n"
    "      tagged Some .v : return $sformatf(\"some %0d\", v);\n"
    "      tagged None : return \"none\";\n"
    "    endcase\n"
    "    return \"?\";\n"
    "  endfunction\n"
    "  function void show(); $display(\"%p\", o); endfunction\n"
    "  function int bad(); return o.None; endfunction\n"
    "endclass\n";

TEST(ObjectPropertySim, TaggedUnionPropertyPrintsItsTagWithP) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kOptBox) +
                           "module t;\n"
                           "  Box b, c;\n"
                           "  initial begin\n"
                           "    b = new; c = new; b.set(9); c.set(4);\n"
                           "    b.show(); $display(\"%p\", c.o);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "'{Some:9}\n'{Some:4}\n");
}

TEST(ObjectPropertySim, ShallowCopyKeepsTaggedUnionPropertyTag) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kOptBox) + "module t;\n"
                                        "  Box b, c;\n"
                                        "  initial begin\n"
                                        "    b = new; b.set(9);\n"
                                        "    c = new b;\n"
                                        "    $display(\"%p %p\", b.o, c.o);\n"
                                        "    c.clear();\n"
                                        "    $display(\"%s %s\", b.describe(), "
                                        "c.describe());\n"
                                        "  end\n"
                                        "endmodule\n",
                 f),
      "'{Some:9} '{Some:9}\nsome 9 none\n");
}

TEST(ObjectPropertySim, TaggedUnionPropertyMatchesItsTagInMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kOptBox) +
                           "module t;\n"
                           "  Box b;\n"
                           "  initial begin\n"
                           "    b = new; b.set(9); $display(\"%s\", "
                           "b.describe());\n"
                           "    b.clear(); $display(\"%s\", b.describe());\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "some 9\nnone\n");
}

TEST(ObjectPropertySim, TaggedUnionPropertyMismatchedReadIsReported) {
  SimFixture f;
  RunCapture(std::string(kOptBox) +
                 "module t;\n"
                 "  Box b;\n"
                 "  int r;\n"
                 "  initial begin b = new; b.set(9); r = b.bad(); end\n"
                 "endmodule\n",
             f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member 'None' of "
                            "tagged union 'o' which currently has tag 'Some'",
                            14, "11.9"));
}

}  // namespace
