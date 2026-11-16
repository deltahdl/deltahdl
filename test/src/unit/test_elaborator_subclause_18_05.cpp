#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

void ExpectNameNotUnique(const char* src, uint32_t line, const char* name = "c",
                         const char* cls = "C") {
  ElabFixture f;
  EXPECT_FALSE(ElabOk(src, f));
  const std::string kMessage = std::string("constraint block name '") + name +
                               "' is not unique within class '" + cls + "'";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, line, "18.5"));
}

TEST(ConstraintBlockNames, TwoImplicitPrototypesOfOneNameRejected) {
  ExpectNameNotUnique(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c;\n"
      "  constraint c;\n"
      "endclass\n"
      "constraint C::c { x > 0; }\n"
      "module m; endmodule\n",
      4);
}

TEST(ConstraintBlockNames, ImplicitAndExplicitPrototypeOfOneNameRejected) {
  ExpectNameNotUnique(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint C::c { x > 0; }\n"
      "module m; endmodule\n",
      4);
}

TEST(ConstraintBlockNames, OnePrototypeWithItsExternalBlockAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m; endmodule\n"));
}

TEST(ConstraintBlockNames, StaticAndNonStaticBlockOfOneNameRejected) {
  ExpectNameNotUnique(
      "class C;\n"
      "  rand int x;\n"
      "  static constraint c { x > 0; }\n"
      "  constraint c { x < 10; }\n"
      "endclass\n"
      "module m; endmodule\n",
      4);
}

TEST(ConstraintBlockNames, StaticAndNonStaticBlocksOfDistinctNamesAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint s { x > 0; }\n"
             "  constraint c { x < 10; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ConstraintBlockNames, DuplicateNameInAPackageClassRejected) {
  ExpectNameNotUnique(
      "package p;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    constraint c { x > 0; }\n"
      "    constraint c { x < 10; }\n"
      "  endclass\n"
      "endpackage\n"
      "module m; endmodule\n",
      5);
}

TEST(ConstraintBlockNames, DistinctNamesInAPackageClassAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  class C;\n"
             "    rand int x;\n"
             "    constraint lo { x > 0; }\n"
             "    constraint hi { x < 10; }\n"
             "  endclass\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(ConstraintBlockNames, DuplicateNameInAModuleClassRejected) {
  ExpectNameNotUnique(
      "module m;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    constraint c { x > 0; }\n"
      "    constraint c { x < 10; }\n"
      "  endclass\n"
      "endmodule\n",
      5);
}

TEST(ConstraintBlockNames, DistinctNamesInAModuleClassAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  class C;\n"
             "    rand int x;\n"
             "    constraint lo { x > 0; }\n"
             "    constraint hi { x < 10; }\n"
             "  endclass\n"
             "endmodule\n"));
}

TEST(ConstraintBlockNames, DuplicateNameInAGenerateBlockClassRejected) {
  ExpectNameNotUnique(
      "module m;\n"
      "  if (1) begin : g\n"
      "    class C;\n"
      "      rand int x;\n"
      "      constraint c { x > 0; }\n"
      "      constraint c { x < 10; }\n"
      "    endclass\n"
      "  end\n"
      "endmodule\n",
      6);
}

TEST(ConstraintBlockNames, DistinctNamesInAGenerateBlockClassAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  if (1) begin : g\n"
             "    class C;\n"
             "      rand int x;\n"
             "      constraint lo { x > 0; }\n"
             "      constraint hi { x < 10; }\n"
             "    endclass\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConstraintBlockNames, DuplicateNameInANestedClassRejected) {
  ExpectNameNotUnique(
      "class O;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    constraint c { x > 0; }\n"
      "    constraint c { x < 10; }\n"
      "  endclass\n"
      "endclass\n"
      "module m; endmodule\n",
      5);
}

TEST(ConstraintBlockNames, NestedClassSharingItsOuterClassNameAccepted) {
  EXPECT_TRUE(
      ElabOk("class O;\n"
             "  rand int y;\n"
             "  constraint c { y > 0; }\n"
             "  class C;\n"
             "    rand int x;\n"
             "    constraint c { x < 10; }\n"
             "  endclass\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
