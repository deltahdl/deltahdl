#include "fixture_elaborator.h"

namespace {

// §33.4.2: an instance clause that names a path inside a hierarchy
// already delegated to another config (via `instance ... use ...:config`)
// is an error.  This is the LRM's worked example: the inner `instance
// top.bot.a1 liblist lib4;` lies under `top.bot`, which has been handed
// off to `lib1.bot:config`.
TEST(ConfigHierarchicalRules,
     InstancePathInsideDelegatedHierarchyIsRejected) {
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

// Positive control: an instance rule on a disjoint subhierarchy is
// allowed.
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

// Positive control: a `:config`-bound instance with no further
// instance rules underneath it elaborates cleanly.
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

// Two `:config` delegations that themselves overlap (a delegated path
// nested inside another delegated path) are also forbidden by the
// "occurs within a hierarchy specified by another config" wording.
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

}  // namespace
