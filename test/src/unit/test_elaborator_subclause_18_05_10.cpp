#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

void ExpectStaticReport(const std::string& src, const char* message,
                        uint32_t line) {
  ElabFixture f;
  EXPECT_FALSE(ElabOk(src, f)) << src;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "18.5.10"))
      << src;
}

const char* const kBodyDisagrees =
    "external constraint block 'C::c' and its prototype disagree on the "
    "'static' qualifier";
const char* const kOverrideMismatch =
    "constraint 'c' overriding a pure constraint shall match its 'static' "
    "qualification";

std::string ExternPrototype(const std::string& prototype,
                            const std::string& body) {
  return "class C;\n"
         "  rand int x;\n"
         "  " +
         prototype +
         "\n"
         "endclass\n" +
         body +
         " { x > 0; }\n"
         "module m;\n"
         "endmodule\n";
}

TEST(StaticConstraint, AnExternStaticPrototypeWithANonStaticBodyIsRejected) {
  ExpectStaticReport(
      ExternPrototype("extern static constraint c;", "constraint C::c"),
      kBodyDisagrees, 5);
}

TEST(StaticConstraint, AnExternPrototypeWithAStaticBodyIsRejected) {
  ExpectStaticReport(
      ExternPrototype("extern constraint c;", "static constraint C::c"),
      kBodyDisagrees, 5);
}

TEST(StaticConstraint, AnExternStaticPrototypeWithAStaticBodyIsAccepted) {
  EXPECT_TRUE(ElabOk(ExternPrototype("extern static constraint c;",
                                     "static constraint C::c")));
}

TEST(StaticConstraint, AStaticPrototypeWithADynamicOverrideIsRejected) {
  ExpectStaticReport(
      ExternPrototype("static constraint :initial c;",
                      "static constraint :initial C::c"),
      "static constraint 'c' shall not carry a dynamic override specifier", 3);
}

std::string PureOverride(const std::string& pure,
                         const std::string& derived_items,
                         const std::string& after = "") {
  return "virtual class B;\n"
         "  rand int x;\n"
         "  " +
         pure +
         "\n"
         "endclass\n"
         "class D extends B;\n"
         "  " +
         derived_items +
         "\n"
         "endclass\n" +
         after +
         "module m;\n"
         "endmodule\n";
}

TEST(StaticConstraint, AStaticPureOverriddenByANonStaticPrototypeIsRejected) {
  ExpectStaticReport(PureOverride("pure static constraint c;", "constraint c;",
                                  "constraint D::c { x > 0; }\n"),
                     kOverrideMismatch, 6);
}

TEST(StaticConstraint, AStaticPureOverriddenByAStaticPrototypeIsAccepted) {
  EXPECT_TRUE(
      ElabOk(PureOverride("pure static constraint c;", "static constraint c;",
                          "static constraint D::c { x > 0; }\n")));
}

std::string AbstractRedeclaration(const std::string& redeclared) {
  return "virtual class B;\n"
         "  rand int x;\n"
         "  pure static constraint c;\n"
         "endclass\n"
         "virtual class D extends B;\n"
         "  " +
         redeclared +
         "\n"
         "endclass\n"
         "module m;\n"
         "endmodule\n";
}

TEST(StaticConstraint, DISABLED_AStaticPureRedeclaredPureNonStaticIsRejected) {
  ExpectStaticReport(AbstractRedeclaration("pure constraint c;"),
                     kOverrideMismatch, 6);
}

TEST(StaticConstraint, AStaticPureRedeclaredPureStaticIsAccepted) {
  EXPECT_TRUE(ElabOk(AbstractRedeclaration("pure static constraint c;")));
}

std::string TwoLevelOverride(const std::string& pure,
                             const std::string& block) {
  return "virtual class B;\n"
         "  rand int x;\n"
         "  " +
         pure +
         "\n"
         "endclass\n"
         "virtual class M extends B;\n"
         "endclass\n"
         "class D extends M;\n"
         "  " +
         block +
         "\n"
         "endclass\n"
         "module m;\n"
         "endmodule\n";
}

TEST(StaticConstraint, AnOverrideTwoLevelsDownIsHeldToThePureQualification) {
  ExpectStaticReport(
      TwoLevelOverride("pure static constraint c;", "constraint c { x > 0; }"),
      kOverrideMismatch, 8);
  ExpectStaticReport(
      TwoLevelOverride("pure constraint c;", "static constraint c { x > 0; }"),
      kOverrideMismatch, 8);
}

TEST(StaticConstraint, AMatchingOverrideTwoLevelsDownIsAccepted) {
  EXPECT_TRUE(ElabOk(TwoLevelOverride("pure static constraint c;",
                                      "static constraint c { x > 0; }")));
  EXPECT_TRUE(ElabOk(
      TwoLevelOverride("pure constraint c;", "constraint c { x > 0; }")));
}

}  // namespace
