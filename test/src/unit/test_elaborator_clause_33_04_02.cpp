#include "fixture_elaborator.h"

namespace {

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

}
