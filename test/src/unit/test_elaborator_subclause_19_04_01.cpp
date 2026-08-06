#include "elaborator/covergroup_inheritance.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §19.4.1: it shall be an error to use the extends declaration when the named
// covergroup has previously been defined in a base class of the enclosing
// class. Here base defines covergroup g1 and the derived class extends it, so
// elaboration succeeds.
TEST(EmbeddedCovergroupInheritance, ExtendsBaseDefinedInBaseClassOk) {
  EXPECT_TRUE(
      ElabOk("class base;\n"
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

// §19.4.1: it shall be an error to use the extends declaration if the named
// covergroup has not previously been defined in a base class. The base class
// here defines no covergroup g1, so the derived extends is illegal.
TEST(EmbeddedCovergroupInheritance, ExtendsBaseNotInBaseClassError) {
  EXPECT_FALSE(
      ElabOk("class base;\n"
             "  bit a;\n"
             "endclass\n"
             "class derived extends base;\n"
             "  bit d;\n"
             "  covergroup extends g1;\n"
             "    coverpoint d;\n"
             "  endgroup\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4.1: a covergroup defined in the deriving class itself does not satisfy
// the requirement; the base covergroup must come from a base class. A class
// with no base class cannot legally use the extends form.
TEST(EmbeddedCovergroupInheritance, ExtendsWithoutBaseClassError) {
  EXPECT_FALSE(
      ElabOk("class lonely;\n"
             "  bit d;\n"
             "  covergroup extends g1;\n"
             "    coverpoint d;\n"
             "  endgroup\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4.1: the base covergroup must be defined in a base class of the enclosing
// class — the search follows the inheritance chain, not the whole design. A
// covergroup of the matching name declared in an unrelated sibling class is not
// visible to the extends form, so the derived covergroup is still illegal.
TEST(EmbeddedCovergroupInheritance, ExtendsBaseInUnrelatedClassError) {
  EXPECT_FALSE(
      ElabOk("class other;\n"
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
             "module m; endmodule\n"));
}

// §19.4.1: the base covergroup may sit further up the inheritance chain, not
// only in the immediate base class. A grandchild may extend a covergroup
// defined in its grandparent.
TEST(EmbeddedCovergroupInheritance, ExtendsBaseInGrandparentOk) {
  EXPECT_TRUE(
      ElabOk("class gp;\n"
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

// §19.4.1: a derived covergroup in one class may itself act as the base
// covergroup for inheritance in another class. Here class b derives g1 from a,
// and class c derives g1 again from b; the validator accepts the whole chain
// because g1 originates in a base class at every level.
TEST(EmbeddedCovergroupInheritance, ExtendsChainAcrossMultipleClassesOk) {
  EXPECT_TRUE(
      ElabOk("class a;\n"
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

// §19.4.1: a derived covergroup may itself act as the base covergroup for
// inheritance in another class, so the inheritance chain has no fixed depth.
TEST(EmbeddedCovergroupInheritance, DerivedCanBeExtendedAgain) {
  EXPECT_TRUE(DerivedCovergroupCanBeExtended());
}

// §19.4.1: a derived covergroup replaces the base instance, so once it exists
// every reference to the shared name resolves to the derived instance, whether
// the reference appears in the deriving class or in a base class.
TEST(EmbeddedCovergroupInheritance, ReferencesResolveToDerivedInstance) {
  EXPECT_TRUE(CovergroupReferenceResolvesToDerived(
      true, CovergroupReferenceSite::kDerivedClass));
  EXPECT_TRUE(CovergroupReferenceResolvesToDerived(
      true, CovergroupReferenceSite::kBaseClass));
  // With no derived covergroup, references resolve to the base instance.
  EXPECT_FALSE(CovergroupReferenceResolvesToDerived(
      false, CovergroupReferenceSite::kBaseClass));
}

// §19.4.1: unless overridden, every base covergroup component is considered to
// also belong to the derived covergroup; an overridden component does not.
TEST(EmbeddedCovergroupInheritance, BaseComponentInheritedUnlessOverridden) {
  EXPECT_TRUE(BaseComponentBelongsToDerived(/*overridden_in_derived=*/false));
  EXPECT_FALSE(BaseComponentBelongsToDerived(/*overridden_in_derived=*/true));
}

// §19.4.1: a derived coverpoint with a name new to the base is an additional
// coverpoint; a derived coverpoint whose name matches a base coverpoint
// overrides it.
TEST(EmbeddedCovergroupInheritance, DerivedCoverpointRoleByName) {
  EXPECT_EQ(ClassifyDerivedCoverpoint(/*name_exists_in_base=*/false),
            DerivedCoverpointRole::kAdditional);
  EXPECT_EQ(ClassifyDerivedCoverpoint(/*name_exists_in_base=*/true),
            DerivedCoverpointRole::kOverride);
}

// §19.4.1: the derived covergroup's coverpoint set is every inherited base
// coverpoint plus the derived coverpoints with new names; a same-named derived
// coverpoint replaces the base one in place rather than adding a duplicate.
TEST(EmbeddedCovergroupInheritance, DerivedCoverpointSetComposition) {
  std::vector<std::string> base = {"a", "b", "c"};
  std::vector<std::string> derived = {"c", "d"};  // c overrides, d is new
  auto result = DerivedCovergroupCoverpoints(base, derived);
  std::vector<std::string> expected = {"a", "b", "c", "d"};
  EXPECT_EQ(result, expected);
}

// §19.4.1: when the base covergroup has a list of arguments, the derived
// covergroup implicitly has that same argument list.
TEST(EmbeddedCovergroupInheritance, DerivedInheritsBaseArguments) {
  std::vector<std::string> base_args = {"arg", "clk"};
  EXPECT_EQ(DerivedCovergroupArguments(base_args), base_args);
}

// §19.4.1: when the base covergroup specifies a coverage event, the derived
// covergroup shall use that same coverage event.
TEST(EmbeddedCovergroupInheritance, DerivedUsesBaseCoverageEvent) {
  EXPECT_EQ(DerivedCovergroupCoverageEvent("@(posedge clk)"), "@(posedge clk)");
}

// §19.4.1: an option specified in the derived covergroup that is also specified
// in the base covergroup overrides the base value; an option not specified in
// the derived covergroup does not override.
TEST(EmbeddedCovergroupInheritance, OptionOverrideDetection) {
  InheritedCoverageOption both;
  both.base_specifies = true;
  both.derived_specifies = true;
  EXPECT_TRUE(DerivedOptionOverridesBase(both));

  InheritedCoverageOption base_only;
  base_only.base_specifies = true;
  EXPECT_FALSE(DerivedOptionOverridesBase(base_only));
}

// §19.4.1: the derived covergroup uses its own value for an option it
// specifies; a base option the derived does not specify still applies.
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

}  // namespace
