#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstraintInheritance, InitialOverridingBaseRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :initial c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint 'c' declared ':initial' overrides a "
                            "constraint of the same name in a base class",
                            6, "18.5.2"));
}

TEST(ConstraintInheritance, InitialOnFreshConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :initial c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, ExtendsWithoutBaseRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :extends c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint 'c' declared ':extends' does not "
                            "override a constraint in a base class",
                            5, "18.5.2"));
}

TEST(ConstraintInheritance, ExtendsOverridingBaseAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :extends c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, ReplacingFinalBaseRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint :final c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constraint 'c' replaces a base class constraint declared ':final'", 6,
      "18.5.2"));
}

TEST(ConstraintInheritance, ExtendsFinalOverridingAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :extends :final c { x < 5; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, PureConstraintInNonAbstractRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure constraint 'c' needs an abstract class, and "
                            "class 'C' is not declared virtual",
                            3, "18.5.2"));
}

TEST(ConstraintInheritance, PureConstraintInAbstractAccepted) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, NonAbstractMissingPureImplRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "non-abstract class 'D' does not implement inherited pure constraint 'c'",
      5, "18.5.2"));
}

TEST(ConstraintInheritance, NonAbstractImplementsPureAccepted) {
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

TEST(ConstraintInheritance, AbstractPureReplacesInheritedAccepted) {
  EXPECT_TRUE(
      ElabOk("class B;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "virtual class D extends B;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, AbstractIntermediateDefersPureObligation) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "virtual class M2 extends B;\n"
             "endclass\n"
             "class D extends M2;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, OverriddenPureNotRequiredInFurtherSubclass) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class E extends D;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, FinalBaseInheritedWithoutReplacementAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint :final c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint d { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, InitialFinalOnFreshConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :initial :final c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, PrototypeAndExternalSpecifierMismatchRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint :final c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::c' and its "
                            "prototype disagree on dynamic override specifiers",
                            5, "18.5.2"));
}

TEST(ConstraintInheritance, PrototypeAndExternalSpecifierMatchAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint :final c;\n"
             "endclass\n"
             "constraint :final C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, PureConstraintWithExternalBlockRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("virtual class C;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::c' conflicts with a "
                            "pure constraint of the same name",
                            5, "18.5.2"));
}

TEST(ConstraintInheritance, PureConstraintWithSameClassBlockRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("virtual class C;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint 'c' in class 'C' conflicts with a pure "
                            "constraint of the same name",
                            4, "18.5.2"));
}

TEST(ConstraintInheritance, PureConstraintWithSameClassPrototypeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("virtual class C;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "  constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint 'c' in class 'C' conflicts with a pure "
                            "constraint of the same name",
                            4, "18.5.2"));
}

TEST(ConstraintInheritance, PrototypeInitialMismatchRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class C extends Base;\n"
             "  constraint :initial c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::c' and its "
                            "prototype disagree on dynamic override specifiers",
                            7, "18.5.2"));
}

TEST(ConstraintInheritance, PrototypeExtendsMismatchRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class C extends Base;\n"
             "  constraint :extends c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::c' and its "
                            "prototype disagree on dynamic override specifiers",
                            8, "18.5.2"));
}

TEST(ConstraintInheritance, DerivedPlainOverrideAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance,
     AbstractIntermediateOverridesInheritedPureAccepted) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "virtual class M extends B;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class D extends M;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, PrototypeInitialMatchAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint :initial c;\n"
             "endclass\n"
             "constraint :initial C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, DerivedPrototypeReplacesBaseAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint c;\n"
             "endclass\n"
             "constraint Derived::c { x < 10; }\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, NonAbstractImplementsPureViaPrototypeAccepted) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c;\n"
             "endclass\n"
             "constraint D::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, PrototypeExtendsMatchAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class C extends Base;\n"
             "  constraint :extends c;\n"
             "endclass\n"
             "constraint :extends C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintInheritance, ExternalBlockSpecifierWithoutPrototypeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c;\n"
             "endclass\n"
             "constraint :final C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::c' and its "
                            "prototype disagree on dynamic override specifiers",
                            5, "18.5.2"));
}

}  // namespace
