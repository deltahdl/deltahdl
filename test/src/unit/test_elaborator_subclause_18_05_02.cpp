#include <gtest/gtest.h>

#include <string>

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

void ExpectInheritanceReport(const std::string& classes, const std::string& msg,
                             int line) {
  ElabFixture f;
  ElabOk(classes + "module m;\nendmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, line, "18.5.2"))
      << classes;
}

void ExpectInheritanceAccepted(const std::string& classes) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk(classes + "module m;\nendmodule\n", f)) << classes;
}

const char* const kDisagree =
    "external constraint block 'C::c' and its prototype disagree on dynamic "
    "override specifiers";
const char* const kBase =
    "class B;\n"
    "  rand int x;\n"
    "  constraint c { x > 0; }\n"
    "endclass\n";

TEST(ConstraintSpecifierAgreement, InitialOnTheBlockOnlyRejected) {
  ExpectInheritanceReport(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c;\n"
      "endclass\n"
      "constraint :initial C::c { x > 0; }\n",
      kDisagree, 5);
}

TEST(ConstraintSpecifierAgreement, ExtendsOnTheBlockOnlyRejected) {
  ExpectInheritanceReport(std::string(kBase) +
                              "class C extends B;\n"
                              "  constraint c;\n"
                              "endclass\n"
                              "constraint :extends C::c { x > 1; }\n",
                          kDisagree, 8);
}

TEST(ConstraintSpecifierAgreement, InitialPrototypeWithExtendsBlockRejected) {
  ExpectInheritanceReport(std::string(kBase) +
                              "class C extends B;\n"
                              "  constraint :initial c;\n"
                              "endclass\n"
                              "constraint :extends C::c { x > 1; }\n",
                          kDisagree, 8);
}

TEST(ConstraintSpecifierAgreement,
     InitialFinalPrototypeWithInitialBlockRejected) {
  ExpectInheritanceReport(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :initial :final c;\n"
      "endclass\n"
      "constraint :initial C::c { x > 0; }\n",
      kDisagree, 5);
}

TEST(ConstraintSpecifierAgreement, ExternFinalPrototypeWithPlainBlockRejected) {
  ExpectInheritanceReport(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint :final c;\n"
      "endclass\n"
      "constraint C::c { x > 0; }\n",
      kDisagree, 5);
}

TEST(ConstraintSpecifierAgreement, MatchingCombinedSpecifiersAccepted) {
  ExpectInheritanceAccepted(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :initial :final c;\n"
      "endclass\n"
      "constraint :initial :final C::c { x > 0; }\n");
  ExpectInheritanceAccepted(std::string(kBase) +
                            "class C extends B;\n"
                            "  constraint :extends :final c;\n"
                            "endclass\n"
                            "constraint :extends :final C::c { x > 1; }\n");
}

const char* const kFinalBase =
    "class B;\n"
    "  rand int x;\n"
    "  constraint :final c { x > 0; }\n"
    "endclass\n";
const char* const kReplacesFinal =
    "constraint 'c' replaces a base class constraint declared ':final'";

TEST(FinalConstraintReplacement, ReplacedByAPrototypeRejected) {
  ExpectInheritanceReport(std::string(kFinalBase) +
                              "class D extends B;\n"
                              "  constraint c;\n"
                              "endclass\n"
                              "constraint D::c { x > 1; }\n",
                          kReplacesFinal, 6);
}

TEST(FinalConstraintReplacement, ReplacedByAnExtendsBlockRejected) {
  ExpectInheritanceReport(std::string(kFinalBase) +
                              "class D extends B;\n"
                              "  constraint :extends c { x > 1; }\n"
                              "endclass\n",
                          kReplacesFinal, 6);
}

TEST(FinalConstraintReplacement, ReplacedByAPureConstraintRejected) {
  ExpectInheritanceReport(std::string(kFinalBase) +
                              "virtual class D extends B;\n"
                              "  pure constraint c;\n"
                              "endclass\n",
                          kReplacesFinal, 6);
}

TEST(FinalConstraintReplacement, ReplacedInAGrandchildRejected) {
  ExpectInheritanceReport(std::string(kFinalBase) +
                              "class M extends B;\n"
                              "endclass\n"
                              "class D extends M;\n"
                              "  constraint c { x > 1; }\n"
                              "endclass\n",
                          kReplacesFinal, 8);
}

TEST(FinalConstraintReplacement, AFinalPrototypeCompletedThenReplacedRejected) {
  ExpectInheritanceReport(
      "class B;\n"
      "  rand int x;\n"
      "  constraint :final c;\n"
      "endclass\n"
      "constraint :final B::c { x > 0; }\n"
      "class D extends B;\n"
      "  constraint c { x > 1; }\n"
      "endclass\n",
      kReplacesFinal, 7);
}

const char* const kExtendsNothing =
    "constraint 'c' declared ':extends' does not override a constraint in a "
    "base class";
const char* const kNoCBase =
    "class B;\n"
    "  rand int x;\n"
    "endclass\n";

TEST(ExtendsConstraintOverride, AnExtendsPrototypeWithNoBaseRejected) {
  ExpectInheritanceReport(std::string(kNoCBase) +
                              "class D extends B;\n"
                              "  constraint :extends c;\n"
                              "endclass\n"
                              "constraint :extends D::c { x > 0; }\n",
                          kExtendsNothing, 5);
}

TEST(ExtendsConstraintOverride, ExtendsFinalWithNoBaseRejected) {
  ExpectInheritanceReport(std::string(kNoCBase) +
                              "class D extends B;\n"
                              "  constraint :extends :final c { x > 0; }\n"
                              "endclass\n",
                          kExtendsNothing, 5);
}

TEST(ExtendsConstraintOverride, ExtendsInAClassExtendingNothingRejected) {
  ExpectInheritanceReport(
      "class D;\n"
      "  rand int x;\n"
      "  constraint :extends c { x > 0; }\n"
      "endclass\n",
      kExtendsNothing, 3);
}

TEST(ExtendsConstraintOverride, ExtendsOverridingAGrandparentAccepted) {
  ExpectInheritanceAccepted(std::string(kBase) +
                            "class M extends B;\n"
                            "endclass\n"
                            "class D extends M;\n"
                            "  constraint :extends c { x > 1; }\n"
                            "endclass\n");
}

const char* const kInitialOverrides =
    "constraint 'c' declared ':initial' overrides a constraint of the same "
    "name in a base class";

TEST(InitialConstraintOverride, AnInitialPrototypeOverridingRejected) {
  ExpectInheritanceReport(std::string(kBase) +
                              "class D extends B;\n"
                              "  constraint :initial c;\n"
                              "endclass\n"
                              "constraint :initial D::c { x > 1; }\n",
                          kInitialOverrides, 6);
}

TEST(InitialConstraintOverride, AnInitialBlockOverridingAGrandparentRejected) {
  ExpectInheritanceReport(std::string(kBase) +
                              "class M extends B;\n"
                              "endclass\n"
                              "class D extends M;\n"
                              "  constraint :initial c { x > 1; }\n"
                              "endclass\n",
                          kInitialOverrides, 8);
}

TEST(InitialConstraintOverride, InitialFinalOverridingRejected) {
  ExpectInheritanceReport(std::string(kBase) +
                              "class D extends B;\n"
                              "  constraint :initial :final c { x > 1; }\n"
                              "endclass\n",
                          kInitialOverrides, 6);
}

TEST(InitialConstraintOverride, AnInitialPureConstraintOverridingRejected) {
  ExpectInheritanceReport(std::string(kBase) +
                              "virtual class D extends B;\n"
                              "  pure constraint :initial c;\n"
                              "endclass\n",
                          kInitialOverrides, 6);
}

TEST(InitialConstraintOverride, AnInitialPrototypeOnANewNameAccepted) {
  ExpectInheritanceAccepted(std::string(kBase) +
                            "class D extends B;\n"
                            "  constraint :initial k;\n"
                            "endclass\n"
                            "constraint :initial D::k { x > 1; }\n");
}

const char* const kConflictsWithPure =
    "constraint 'c' in class 'C' conflicts with a pure constraint of the same "
    "name";

TEST(PureConstraintConflicts, AnExternPrototypeOfTheNameRejected) {
  ExpectInheritanceReport(
      "virtual class C;\n"
      "  rand int x;\n"
      "  pure constraint c;\n"
      "  extern constraint c;\n"
      "endclass\n",
      kConflictsWithPure, 4);
}

TEST(PureConstraintConflicts, AStaticBlockBesideAPureStaticRejected) {
  ExpectInheritanceReport(
      "virtual class C;\n"
      "  rand int x;\n"
      "  pure static constraint c;\n"
      "  static constraint c { x > 0; }\n"
      "endclass\n",
      kConflictsWithPure, 4);
}

TEST(PureConstraintConflicts, ADifferentlyNamedBlockAccepted) {
  ExpectInheritanceAccepted(
      "virtual class C;\n"
      "  rand int x;\n"
      "  pure constraint c;\n"
      "  constraint k { x > 0; }\n"
      "endclass\n");
}

TEST(PureConstraintObligation, AGrandchildThroughAnAbstractClassRejected) {
  ExpectInheritanceReport(
      "virtual class B;\n"
      "  rand int x;\n"
      "  pure constraint c;\n"
      "endclass\n"
      "virtual class M extends B;\n"
      "endclass\n"
      "class D extends M;\n"
      "endclass\n",
      "non-abstract class 'D' does not implement inherited pure constraint 'c'",
      7);
}

TEST(PureConstraintObligation, OneOfTwoPureConstraintsMissingRejected) {
  ElabFixture f;
  ElabOk(
      "virtual class B;\n"
      "  rand int x;\n"
      "  pure constraint c;\n"
      "  pure constraint k;\n"
      "endclass\n"
      "class D extends B;\n"
      "  constraint c { x > 0; }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "non-abstract class 'D' does not implement inherited pure constraint 'k'",
      6, "18.5.2"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_EQ(d.message.find("pure constraint 'c'"), std::string::npos)
        << d.message;
  }
}

TEST(PureConstraintObligation, AConstraintRedeclaredPureMustBeImplemented) {
  ExpectInheritanceReport(
      std::string(kBase) +
          "virtual class M extends B;\n"
          "  pure constraint c;\n"
          "endclass\n"
          "class D extends M;\n"
          "endclass\n",
      "non-abstract class 'D' does not implement inherited pure constraint 'c'",
      8);
}

const char* const kNeedsAbstract =
    "pure constraint 'c' needs an abstract class, and class 'C' is not "
    "declared virtual";

TEST(PureConstraintPlacement, ANonAbstractClassExtendingAVirtualRejected) {
  ExpectInheritanceReport(
      "virtual class B;\n"
      "  rand int x;\n"
      "endclass\n"
      "class C extends B;\n"
      "  pure constraint c;\n"
      "endclass\n",
      kNeedsAbstract, 5);
}

TEST(PureConstraintPlacement, ANonAbstractClassExtendingAConcreteRejected) {
  ExpectInheritanceReport(std::string(kNoCBase) +
                              "class C extends B;\n"
                              "  pure constraint c;\n"
                              "endclass\n",
                          kNeedsAbstract, 5);
}

TEST(PureConstraintPlacement, InAPackageAModuleAndANestedClassRejected) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    pure constraint c;\n"
      "  endclass\n"
      "endpackage\n"
      "class O;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    pure constraint c;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    pure constraint c;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  for (int line : {4, 10, 16}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNeedsAbstract, line, "18.5.2"))
        << line;
  }
}

TEST(PureConstraintPlacement, AnAbstractClassExtendingAConcreteAccepted) {
  ExpectInheritanceAccepted(std::string(kNoCBase) +
                            "virtual class C extends B;\n"
                            "  pure constraint c;\n"
                            "endclass\n");
}

TEST(PureConstraintPlacement, APureStaticInANonAbstractClassRejected) {
  ExpectInheritanceReport(
      "class C;\n"
      "  rand int x;\n"
      "  pure static constraint c;\n"
      "endclass\n",
      kNeedsAbstract, 3);
}

}  // namespace
