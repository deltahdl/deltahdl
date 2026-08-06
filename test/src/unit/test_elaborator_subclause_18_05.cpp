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
