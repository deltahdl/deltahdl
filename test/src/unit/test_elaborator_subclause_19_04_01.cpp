#include <gtest/gtest.h>

#include <vector>

#include "elaborator/covergroup_inheritance.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EmbeddedCovergroupInheritance, ExtendsBaseDefinedInBaseClassOk) {
  EXPECT_TRUE(
      ElabOk("class base; logic clk;\n"
             "  bit a;\n"
             "  covergroup g1 @(posedge clk);\n"
             "    coverpoint a;\n"
             "  endgroup\n"
             "endclass\n"
             "class derived extends base;\n"
             "  bit d;\n"
             "  covergroup extends g1;\n"
             "    coverpoint d;\n"
             "  endgroup\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(EmbeddedCovergroupInheritance, ExtendsBaseNotInBaseClassError) {
  ElabFixture f;
  ElabOk(
      "class base;\n"
      "  bit a;\n"
      "endclass\n"
      "class derived extends base;\n"
      "  bit d;\n"
      "  covergroup extends g1;\n"
      "    coverpoint d;\n"
      "  endgroup\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "derived covergroup cannot extend 'g1': no "
                    "covergroup of that name is defined in a base class",
                    6, "19.4.1"));
}

TEST(EmbeddedCovergroupInheritance, ExtendsWithoutBaseClassError) {
  ElabFixture f;
  ElabOk(
      "class lonely;\n"
      "  bit d;\n"
      "  covergroup extends g1;\n"
      "    coverpoint d;\n"
      "  endgroup\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "derived covergroup cannot extend 'g1': no "
                    "covergroup of that name is defined in a base class",
                    3, "19.4.1"));
}

TEST(EmbeddedCovergroupInheritance, ExtendsBaseInUnrelatedClassError) {
  ElabFixture f;
  ElabOk(
      "class other; logic clk;\n"
      "  bit a;\n"
      "  covergroup g1 @(posedge clk);\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "endclass\n"
      "class base;\n"
      "  bit b;\n"
      "endclass\n"
      "class derived extends base;\n"
      "  bit d;\n"
      "  covergroup extends g1;\n"
      "    coverpoint d;\n"
      "  endgroup\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "derived covergroup cannot extend 'g1': no "
                    "covergroup of that name is defined in a base class",
                    12, "19.4.1"));
}

TEST(EmbeddedCovergroupInheritance, ExtendsBaseInGrandparentOk) {
  EXPECT_TRUE(
      ElabOk("class gp; logic clk;\n"
             "  bit a;\n"
             "  covergroup g1 @(posedge clk);\n"
             "    coverpoint a;\n"
             "  endgroup\n"
             "endclass\n"
             "class mid extends gp;\n"
             "  bit b;\n"
             "endclass\n"
             "class leaf extends mid;\n"
             "  bit d;\n"
             "  covergroup extends g1;\n"
             "    coverpoint d;\n"
             "  endgroup\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(EmbeddedCovergroupInheritance, ExtendsChainAcrossMultipleClassesOk) {
  EXPECT_TRUE(
      ElabOk("class a; logic clk;\n"
             "  bit x;\n"
             "  covergroup g1 @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "endclass\n"
             "class b extends a;\n"
             "  bit y;\n"
             "  covergroup extends g1;\n"
             "    coverpoint y;\n"
             "  endgroup\n"
             "endclass\n"
             "class c extends b;\n"
             "  bit z;\n"
             "  covergroup extends g1;\n"
             "    coverpoint z;\n"
             "  endgroup\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(EmbeddedCovergroupInheritance, DerivedCanBeExtendedAgain) {
  EXPECT_TRUE(DerivedCovergroupCanBeExtended());
}

TEST(EmbeddedCovergroupInheritance, ReferencesResolveToDerivedInstance) {
  EXPECT_TRUE(CovergroupReferenceResolvesToDerived(
      true, CovergroupReferenceSite::kDerivedClass));
  EXPECT_TRUE(CovergroupReferenceResolvesToDerived(
      true, CovergroupReferenceSite::kBaseClass));
  EXPECT_FALSE(CovergroupReferenceResolvesToDerived(
      false, CovergroupReferenceSite::kBaseClass));
}

TEST(EmbeddedCovergroupInheritance, BaseComponentInheritedUnlessOverridden) {
  EXPECT_TRUE(BaseComponentBelongsToDerived(false));
  EXPECT_FALSE(BaseComponentBelongsToDerived(true));
}

TEST(EmbeddedCovergroupInheritance, DerivedCoverpointRoleByName) {
  EXPECT_EQ(ClassifyDerivedCoverpoint(false),
            DerivedCoverpointRole::kAdditional);
  EXPECT_EQ(ClassifyDerivedCoverpoint(true), DerivedCoverpointRole::kOverride);
}

TEST(EmbeddedCovergroupInheritance, DerivedCoverpointSetComposition) {
  std::vector<std::string> base = {"a", "b", "c"};
  std::vector<std::string> derived = {"c", "d"};
  auto result = DerivedCovergroupCoverpoints(base, derived);
  std::vector<std::string> expected = {"a", "b", "c", "d"};
  EXPECT_EQ(result, expected);
}

TEST(EmbeddedCovergroupInheritance, DerivedInheritsBaseArguments) {
  std::vector<std::string> base_args = {"arg", "clk"};
  EXPECT_EQ(DerivedCovergroupArguments(base_args), base_args);
}

TEST(EmbeddedCovergroupInheritance, DerivedUsesBaseCoverageEvent) {
  EXPECT_EQ(DerivedCovergroupCoverageEvent("@(posedge clk)"), "@(posedge clk)");
}

TEST(EmbeddedCovergroupInheritance, OptionOverrideDetection) {
  InheritedCoverageOption both;
  both.base_specifies = true;
  both.derived_specifies = true;
  EXPECT_TRUE(DerivedOptionOverridesBase(both));

  InheritedCoverageOption base_only;
  base_only.base_specifies = true;
  EXPECT_FALSE(DerivedOptionOverridesBase(base_only));
}

TEST(EmbeddedCovergroupInheritance, EffectiveOptionValue) {
  InheritedCoverageOption overridden;
  overridden.base_specifies = true;
  overridden.base_value = 10;
  overridden.derived_specifies = true;
  overridden.derived_value = 1;
  EXPECT_EQ(EffectiveDerivedOption(overridden), 1);

  InheritedCoverageOption inherited;
  inherited.base_specifies = true;
  inherited.base_value = 10;
  EXPECT_EQ(EffectiveDerivedOption(inherited), 10);
}

TEST(EmbeddedCovergroupInheritance,
     ADerivedCrossNamesTheBasesCoverpointLabels) {
  EXPECT_TRUE(ElabOk(
      "class base;\n"
      "  bit a, b;\n"
      "  covergroup g1;\n"
      "    ca: coverpoint a;\n"
      "    cb: coverpoint b;\n"
      "    x: cross ca, cb;\n"
      "  endgroup\n"
      "endclass\n"
      "class derived extends base;\n"
      "  covergroup extends g1;\n"
      "    x: cross ca, cb { ignore_bins one = binsof(ca) intersect {1}; }\n"
      "  endgroup : g1\n"
      "endclass\n"
      "module m; endmodule\n"));
}

TEST(EmbeddedCovergroupInheritance, ADerivedCrossOfAnUnknownNameIsRefused) {
  ElabFixture f;
  ElabOk(
      "class base;\n"
      "  bit a;\n"
      "  covergroup g1;\n"
      "    ca: coverpoint a;\n"
      "  endgroup\n"
      "endclass\n"
      "class derived extends base;\n"
      "  covergroup extends g1;\n"
      "    x: cross ca, zz;\n"
      "  endgroup : g1\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'zz' is neither a coverpoint of "
                            "covergroup 'g1' nor a variable",
                            9, "19.6"));
}

}  // namespace
