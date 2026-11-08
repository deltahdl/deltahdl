#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstraintBlockNames, DuplicateNameRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  constraint c { x < 10; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constraint block name 'c' is not unique within class 'C'", 4, "18.5"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not unique within class 'C'", 4, "18.5"));
}

TEST(ConstraintBlockNames, DistinctNamesAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint lo { x > 0; }\n"
             "  constraint hi { x < 10; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

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
