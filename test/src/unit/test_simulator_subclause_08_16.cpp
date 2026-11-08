#include <gtest/gtest.h>

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

}  // namespace
