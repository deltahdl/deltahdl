#include <gtest/gtest.h>

#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_config_unit.h"
#include "fixture_elaborator.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

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

// §33.4.2: binding an instance directly to a configuration replaces that
// instance's subtree with the delegated config's hierarchy. Two things follow.
// (A1) The design statement in the delegated config specifies the actual
// binding for the instance: here module `mid` exists in both lib1 (the outer
// config's default liblist) and lib2, and the delegated config's design
// statement is `design lib2.mid`, so the delegated instance must bind to
// lib2.mid rather than the outer default's lib1.mid. (A2) The rules of the
// delegated config -- not the outer config -- govern every subinstance beneath
// it: the delegated config's default liblist (libY) pins `mid`'s child leaf to
// libY, whereas the outer config's default (lib1, which has no leaf) would have
// left it unbound. Observing lib2 on the instance and libY on the grandchild
// proves both halves of the delegation semantics.
TEST(ConfigHierarchicalRules,
     DelegatedConfigDesignStatementAndRulesGovernSubtree) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module leaf; endmodule\n"            // libX
              "module leaf; endmodule\n"            // libY
              "module mid; leaf lf(); endmodule\n"  // lib1
              "module mid; leaf lf(); endmodule\n"  // lib2
              "module top; mid m(); endmodule\n"    // libTop
              "config c;\n"
              "  design top;\n"
              "  default liblist lib1;\n"
              "  instance top.m use lib2.mid:config;\n"
              "endconfig\n"
              "config mid;\n"
              "  design lib2.mid;\n"
              "  default liblist libY;\n"
              "endconfig\n"));
  // The modules in declaration order: the source comments name each.
  u.PlaceModulesInLibraries({"libX", "libY", "lib1", "lib2", "libTop"});

  // Elaborate the outer config `c` (configs[0]); its instance clause delegates
  // top.m to config `mid` (configs[1]) via the ':config' binding.
  //
  // A1: the delegated config's design statement (`design lib2.mid`) specifies
  // the binding, so top.m is lib2.mid -- not lib1.mid from the outer default.
  // A2: the delegated config's rules (default liblist libY) govern the
  // subtree, binding mid's leaf from libY. The outer config's default (lib1)
  // has no leaf, so a libY leaf here can only come from the delegated config.
  ExpectChainBindsChildAndLeaf(u.ElaborateConfig(0), "mid", "lib2", "libY");
}

// §33.4.2 (Claim A, A2): the rules of the delegated config govern the
// subinstances beneath the bound instance -- exercised here through an
// *instance* clause inside the delegated config rather than a default clause,
// which is a distinct code path (the inner instance rule's hierarchical path is
// rewritten from the delegated config's own top onto the outer hierarchy). The
// delegated config `mid` pins its own subinstance `mid.lf` to libY; that rule
// is relocated onto `top.m`, so `top.m.lf` binds from libY. With no default
// liblist in either config, ordinary resolution would take the first-declared
// leaf (libX), so observing libY on the grandchild proves the delegated
// config's instance rule was applied to the subtree.
TEST(ConfigHierarchicalRules, DelegatedConfigInstanceRuleGovernsSubinstance) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module leaf; endmodule\n"            // libX
              "module leaf; endmodule\n"            // libY
              "module mid; leaf lf(); endmodule\n"  // lib2
              "module top; mid m(); endmodule\n"    // libTop
              "config c;\n"
              "  design top;\n"
              "  instance top.m use lib2.mid:config;\n"
              "endconfig\n"
              "config mid;\n"
              "  design lib2.mid;\n"
              "  instance mid.lf liblist libY;\n"
              "endconfig\n"));
  // The modules in declaration order: the source comments name each.
  u.PlaceModulesInLibraries({"libX", "libY", "lib2", "libTop"});

  // Elaborate the outer config `c`; its instance clause delegates top.m to
  // config `mid`, whose instance rule governs top.m's subtree. That rule
  // (instance mid.lf liblist libY), rewritten onto top.m, binds top.m.lf from
  // libY rather than from the first-declared leaf.
  ExpectChainBindsChildAndLeaf(u.ElaborateConfig(0), "mid", "lib2", "libY");
}

}  // namespace
