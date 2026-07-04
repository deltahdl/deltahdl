#include "fixture_simulator.h"
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
  // Success case 1: the source and destination are assignment compatible, i.e.
  // the destination type is the same as or a superclass of the source
  // expression's type. Casting a derived handle into a base-typed destination
  // is that direction, so the cast succeeds and returns 1.
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
  // Success case 1, the "same type" sub-form: the destination and source are
  // the identical class type — the most direct assignment-compatible cast — so
  // $cast succeeds and returns 1. (The superclass-of-source sub-form is covered
  // separately by E2eCastAssignmentCompatibleDirectionSucceeds.)
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// §8.16 / §6.24.2 interweave: the task form of a class-handle downcast that
// succeeds performs the assignment and, the assignment being valid, raises no
// run-time error. This is the positive counterpart to the task form that fails:
// only an invalid cast triggers the diagnostic.
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
  // A successful cast does more than report success: it performs the
  // assignment, so afterwards the destination handle references the very
  // object the source pointed at. Here the base handle b points at a Derived
  // object, the downcast into d2 succeeds, and d2 then refers to the same
  // object as the original derived handle d.
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

}  // namespace
