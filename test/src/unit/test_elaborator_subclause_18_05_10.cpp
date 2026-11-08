#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StaticConstraint, PlainStaticConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(StaticConstraint, StaticWithInitialRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint :initial c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "static constraint 'c' shall not carry a dynamic override specifier", 3,
      "18.5.10"));
}

TEST(StaticConstraint, StaticWithExtendsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  static constraint :extends c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "static constraint 'c' shall not carry a dynamic override specifier", 6,
      "18.5.10"));
}

TEST(StaticConstraint, StaticWithFinalRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint :final c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "static constraint 'c' shall not carry a dynamic override specifier", 3,
      "18.5.10"));
}

TEST(StaticConstraint, StaticPrototypeNonStaticExternalRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::c' and its "
                            "prototype disagree on the 'static' qualifier",
                            5, "18.5.10"));
}

TEST(StaticConstraint, NonStaticPrototypeStaticExternalRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c;\n"
             "endclass\n"
             "static constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::c' and its "
                            "prototype disagree on the 'static' qualifier",
                            5, "18.5.10"));
}

TEST(StaticConstraint, StaticPrototypeAndExternalAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint c;\n"
             "endclass\n"
             "static constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(StaticConstraint, NonStaticPrototypeAndExternalAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(StaticConstraint, StaticPureOverriddenByStaticAccepted) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure static constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  static constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(StaticConstraint, StaticPureOverriddenByNonStaticRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure static constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint 'c' overriding a pure constraint "
                            "shall match its 'static' qualification",
                            6, "18.5.10"));
}

TEST(StaticConstraint, NonStaticPureOverriddenByStaticRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  static constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint 'c' overriding a pure constraint "
                            "shall match its 'static' qualification",
                            6, "18.5.10"));
}

TEST(StaticConstraint, NonStaticPureOverriddenByNonStaticAccepted) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
