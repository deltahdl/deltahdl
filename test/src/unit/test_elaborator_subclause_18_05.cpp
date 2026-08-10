#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.5: constraint block names shall be unique within a class.
TEST(ConstraintBlockNames, DuplicateNameRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  constraint c { x < 10; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §18.5 states the rule this rejection enforces in one sentence: "Constraint
// block names shall be unique within a class." The subclause on the report is
// what tells it from §18.5.2's rule that a derived class constraint of the
// same name replaces the inherited one, which two same-named constraints
// breach only when they sit in different classes of one hierarchy.
TEST(ConstraintBlockNames, DuplicateNameNames18_5) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  constraint c { x < 10; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  const auto* diag = FindDiag(f, "is not unique within class");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "18.5");
}

// Distinct constraint block names within a class are legal.
TEST(ConstraintBlockNames, DistinctNamesAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint lo { x > 0; }\n"
             "  constraint hi { x < 10; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// The same constraint block name may appear in two different classes.
TEST(ConstraintBlockNames, SameNameDifferentClassesAccepted) {
  EXPECT_TRUE(
      ElabOk("class A;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class B;\n"
             "  rand int y;\n"
             "  constraint c { y > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
