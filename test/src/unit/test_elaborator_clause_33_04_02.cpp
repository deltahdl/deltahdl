#include "fixture_elaborator.h"

namespace {

TEST(ConfigHierarchicalRules, InstancePathInsideDelegatedHierarchyIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.bot use lib1.bot:config;\n"
      "  instance top.bot.a1 liblist lib4;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigHierarchicalRules, DisjointInstancePathsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.bot use lib1.bot:config;\n"
      "  instance top.other liblist lib4;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigHierarchicalRules, IsolatedConfigBindingAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.bot use lib1.bot:config;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigHierarchicalRules, NestedDelegationIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a use lib1.outer:config;\n"
      "  instance top.a.b use lib1.inner:config;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// A path that merely shares a leading name fragment with a delegated subtree
// (top.bottom vs. delegated top.bot) is not actually inside that subtree, so
// the hierarchy boundary check must require a full path-segment boundary and
// leave such a sibling accepted.
TEST(ConfigHierarchicalRules, PrefixSiblingPathNotTreatedAsNested) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.bot use lib1.bot:config;\n"
      "  instance top.bottom liblist lib4;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// The error applies regardless of how deep the offending path reaches below
// the delegated subtree, not just at the immediate child level.
TEST(ConfigHierarchicalRules, DeeplyNestedInstancePathIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.bot use lib1.bot:config;\n"
      "  instance top.bot.a1.sub liblist lib4;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
