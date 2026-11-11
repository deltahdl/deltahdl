#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ClassSim, E2eCastFunctionReturnsOneOnSuccess) {
  EXPECT_EQ(RunAndGet("class Base; int x; endclass\n"
                      "class Derived extends Base; int y; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base b;\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    b = d;\n"
                      "    result = $cast(d, b);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, E2eCastAssignmentCompatibleDirectionSucceeds) {
  EXPECT_EQ(RunAndGet("class Base; int x; endclass\n"
                      "class Derived extends Base; int y; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base b;\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    result = $cast(b, d);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, E2eCastSameTypeSucceeds) {
  EXPECT_EQ(RunAndGet("class Base; int x; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base a;\n"
                      "    Base b;\n"
                      "    a = new;\n"
                      "    result = $cast(b, a);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, E2eCastFunctionReturnsZeroOnFailure) {
  EXPECT_EQ(RunAndGet("class Base; endclass\n"
                      "class Derived extends Base; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base b;\n"
                      "    Derived d;\n"
                      "    b = new;\n"
                      "    result = $cast(d, b);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(ClassSim, E2eCastTaskFormFailsWithError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    b = new;\n"
      "    $cast(d, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$cast task could not assign the source expression",
                            8, "6.24.2"));
}

TEST(ClassSim, E2eCastTaskFormSucceedsNoError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    Derived d2;\n"
      "    d = new;\n"
      "    b = d;\n"
      "    $cast(d2, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassSim, E2eCastNullSucceeds) {
  EXPECT_EQ(RunAndGet("class Base; endclass\n"
                      "class Derived extends Base; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    result = $cast(d, null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, E2eCastNullAssignsNull) {
  EXPECT_EQ(RunAndGet("class Base; endclass\n"
                      "class Derived extends Base; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    $cast(d, null);\n"
                      "    result = (d == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, E2eSuccessfulCastWritesDestinationHandle) {
  EXPECT_EQ(RunAndGet("class Base; int x; endclass\n"
                      "class Derived extends Base; int y; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base b;\n"
                      "    Derived d;\n"
                      "    Derived d2;\n"
                      "    d = new;\n"
                      "    b = d;\n"
                      "    $cast(d2, b);\n"
                      "    result = (d2 == d);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, E2eUpcastAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base; int x; endclass\n"
      "class Derived extends Base; int y; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    Base b;\n"
      "    d = new;\n"
      "    b = d;\n"
      "    result = (b != null);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 1u}});
}

TEST(ClassSim, E2eCastDeepHierarchyDowncast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Grand; endclass\n"
      "class Mid extends Grand; endclass\n"
      "class Leaf extends Mid; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Grand g;\n"
      "    Leaf l;\n"
      "    l = new;\n"
      "    g = l;\n"
      "    result = $cast(l, g);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 1u}});
}

TEST(ClassSim, E2eCastDeepHierarchyDowncastFails) {
  EXPECT_EQ(RunAndGet("class Grand; endclass\n"
                      "class Mid extends Grand; endclass\n"
                      "class Leaf extends Mid; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Grand g;\n"
                      "    Leaf l;\n"
                      "    g = new;\n"
                      "    result = $cast(l, g);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(ClassSim, E2eCastFailsIncompatibleTypesEvenIfNull) {
  EXPECT_EQ(RunAndGet("class A; endclass\n"
                      "class B; endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    A a;\n"
                      "    B b;\n"
                      "    result = $cast(a, b);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(ClassSim, E2eCastFromInterfaceClassSourceSucceeds) {
  EXPECT_EQ(RunAndGet("interface class IntfC;\n"
                      "  pure virtual function int get();\n"
                      "endclass\n"
                      "class C implements IntfC;\n"
                      "  virtual function int get(); return 7; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    IntfC ih;\n"
                      "    C c;\n"
                      "    C c2;\n"
                      "    c = new;\n"
                      "    ih = c;\n"
                      "    result = $cast(c2, ih);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, CastReachesTheSubclassObjectBehindAnyHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class B; int v = 1; endclass\n"
      "class D extends B; function new(); v = 2; endfunction endclass\n"
      "class L extends D; function new(); v = 3; endfunction endclass\n"
      "class S extends B; endclass\n"
      "interface class IA; endclass\n"
      "interface class IB; endclass\n"
      "class AB implements IA, IB; endclass\n"
      "class OA implements IA; endclass\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9;\n"
      "  initial begin\n"
      "    B b; D d; L l; S s; IA ia; IB ib; AB ab; OA oa;\n"
      "    l = new; b = l;\n"
      "    r1 = $cast(d, b) + 10 * d.v;\n"
      "    s = new; b = s; d = null;\n"
      "    r2 = $cast(d, b) + 10 * (d == null);\n"
      "    d = new;\n"
      "    r3 = $cast(s, d);\n"
      "    ab = new; ia = ab;\n"
      "    r4 = $cast(ib, ia);\n"
      "    oa = new; ia = oa;\n"
      "    r5 = $cast(ib, ia) + 10 * (ib == ab);\n"
      "    r6 = $cast(ab, ia);\n"
      "    d = new; l = null;\n"
      "    r7 = $cast(l, d) + 10 * (l == null);\n"
      "    b = d;\n"
      "    $cast(b, l);\n"
      "    l = new;\n"
      "    $cast(b, l);\n"
      "    r8 = b.v;\n"
      "    d = new;\n"
      "    r9 = $cast(b, d);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 31u},
                    {"r2", 10u},
                    {"r3", 0u},
                    {"r4", 1u},
                    {"r5", 10u},
                    {"r6", 0u},
                    {"r7", 10u},
                    {"r8", 3u},
                    {"r9", 1u}});
}

TEST(ClassSim, CastDowncastsInEveryPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class B; int v = 1; endclass\n"
      "class D extends B; function new(); v = 2; endfunction endclass\n"
      "package cp;\n"
      "  function automatic int down(B b);\n"
      "    D d;\n"
      "    if (!$cast(d, b)) return 0;\n"
      "    return d.v;\n"
      "  endfunction\n"
      "endpackage\n"
      "class H;\n"
      "  function int down(B b);\n"
      "    D d;\n"
      "    if ($cast(d, b)) return 10 + d.v;\n"
      "    return 5;\n"
      "  endfunction\n"
      "endclass\n"
      "function automatic int cu_down(B b);\n"
      "  D d;\n"
      "  void'($cast(d, b));\n"
      "  return d == null ? 7 : d.v + 20;\n"
      "endfunction\n"
      "program pg(output int r);\n"
      "  initial begin\n"
      "    automatic D d;\n"
      "    automatic B b = new;\n"
      "    r = 40 + $cast(d, b);\n"
      "    d = new; b = d; d = null;\n"
      "    r = r + 10 * $cast(d, b);\n"
      "  end\n"
      "endprogram\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5, r6, r7;\n"
      "  pg p(r7);\n"
      "  initial begin\n"
      "    automatic H h = new;\n"
      "    automatic D dd = new;\n"
      "    automatic B bb = new;\n"
      "    r1 = cp::down(dd);\n"
      "    r2 = cp::down(bb);\n"
      "    r3 = h.down(dd);\n"
      "    r4 = h.down(bb);\n"
      "    r5 = cu_down(dd);\n"
      "    r6 = cu_down(bb);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 2u},
                    {"r2", 0u},
                    {"r3", 12u},
                    {"r4", 5u},
                    {"r5", 22u},
                    {"r6", 7u},
                    {"r7", 50u}});
}

TEST(ClassSim, CastTaskFormReportsEveryCastThatFails) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "class P; endclass\n"
      "class Q extends P; endclass\n"
      "class R extends P; endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    A a; B b; Q q; R r; P p;\n"
      "    $cast(a, b);\n"
      "    q = new;\n"
      "    $cast(p, q);\n"
      "    $cast(r, q);\n"
      "    $cast(q, null);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {9, 12}) {
    EXPECT_TRUE(ReportedError(diags,
                              "$cast task could not assign the source "
                              "expression",
                              kLine, "6.24.2"))
        << kLine;
  }
  for (const int kLine : {11, 13}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
