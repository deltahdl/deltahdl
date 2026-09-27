#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_config_unit.h"
#include "fixture_elaborator.h"
#include "helpers_config_reports.h"
#include "helpers_reported_error.h"

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
  // Elaborating the module runs the hierarchical-rule validation and not the
  // delegation collection, so the "delegates instance ... to unknown config"
  // report is not drawn here; TwoRulesOnOneSourceReportAtTwoPlaces elaborates
  // the configuration to get both. This report stands at the
  // `instance top.bot.a1` clause on line 5 that breaks the nesting rule.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance 'top.bot.a1' in config 'c' lies within "
                            "subhierarchy 'top.bot' that is delegated to "
                            "another config",
                            5, "33.4.2"));
}

// The property that keeps ReportedError's line check independent across §33.4:
// two different rules firing on one source must report at two different places.
// While both stood at the `config` keyword, only the message told them apart,
// so two of ReportedError's three checks did no work on any §33.4.2 case. A fix
// that moved both reports to one new shared line would satisfy every other case
// in this file and fail here, which is why the assertion is on the two lines
// differing rather than on either line's value.
TEST(ConfigHierarchicalRules, TwoRulesOnOneSourceReportAtTwoPlaces) {
  // The configuration is elaborated rather than the module, because the
  // delegation report is raised by CollectConfigDelegationOverrides, which
  // Elaborator::Elaborate reaches only through its ConfigDecl overload.
  // Elaborating `top` runs the hierarchical-rule validation and not that
  // collection, so it draws one of the two reports and cannot show them apart.
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module top; endmodule\n"
              "config c;\n"
              "  design top;\n"
              "  instance top.bot use lib1.bot:config;\n"
              "  instance top.bot.a1 liblist lib4;\n"
              "endconfig\n"));
  u.ElaborateConfig(0);
  // The delegating clause on line 4 draws the unknown-config report, and the
  // nested clause on line 5 draws the subhierarchy report. Both are §33.4.2,
  // and the pair of assertions is the claim: neither line satisfies the other.
  EXPECT_TRUE(
      ReportedError(u.diag.Diagnostics(),
                    "config 'c' delegates instance 'top.bot' to unknown "
                    "config 'bot'",
                    4, "33.4.2"));
  EXPECT_TRUE(ReportedError(u.diag.Diagnostics(),
                            "instance 'top.bot.a1' in config 'c' lies within "
                            "subhierarchy 'top.bot' that is delegated to "
                            "another config",
                            5, "33.4.2"));
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
  // Reported at the nested `instance top.a.b` clause on line 5. The two
  // ':config' bindings draw no report on this path: the delegation collection
  // that would raise one runs only when the configuration itself is
  // elaborated.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance 'top.a.b' in config 'c' lies within "
                            "subhierarchy 'top.a' that is delegated to another "
                            "config",
                            5, "33.4.2"));
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
  // The path two levels below the delegated root, named in the report so the
  // depth the case is about is what the assertion reads. Line 5 is the
  // offending instance clause, where the rule reports.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance 'top.bot.a1.sub' in config 'c' lies "
                            "within subhierarchy 'top.bot' that is delegated "
                            "to another config",
                            5, "33.4.2"));
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

// §33.4.2 (Claim A, A1) again, over the case the two tests above cannot reach:
// the cell the delegated config's design statement names is not the cell the
// instantiation declares. There the instance is written `mid m()` and the
// delegated config designs a cell called `mid`, so a binding that ignored the
// delegation outright and simply resolved the declared name would land on the
// same name and be indistinguishable from one the delegation produced. Here the
// instantiation declares `mid` and the delegated config designs `alt`, which is
// the situation §33.4.1.6's note describes: the binding statement makes the
// unbound instance's module name and the cell name it binds to differ.
//
// The library the name would otherwise reach is left in place -- `mid` really
// is in lib1 and the outer default liblist really does select lib1 -- so the
// design that comes out is `alt` only because the design statement of the
// configuration top.m was handed to specified the binding for it.
TEST(ConfigHierarchicalRules, DelegatedDesignStatementBindsACellOfAnotherName) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module leaf; endmodule\n"            // libX
              "module leaf; endmodule\n"            // libY
              "module alt; leaf lf(); endmodule\n"  // lib2
              "module mid; leaf lf(); endmodule\n"  // lib1
              "module top; mid m(); endmodule\n"    // libTop
              "config c;\n"
              "  design top;\n"
              "  default liblist lib1;\n"
              "  instance top.m use lib2.alt:config;\n"
              "endconfig\n"
              "config alt;\n"
              "  design lib2.alt;\n"
              "  default liblist libY;\n"
              "endconfig\n"));
  // The modules in declaration order: the source comments name each.
  u.PlaceModulesInLibraries({"libX", "libY", "lib2", "lib1", "libTop"});

  // top.m binds lib2.alt, the cell the delegated config designs, rather than
  // the lib1.mid its own instantiation declares; the delegated config's rules
  // then govern the subtree, so alt's leaf comes from libY.
  ExpectChainBindsChildAndLeaf(u.ElaborateConfig(0), "alt", "lib2", "libY");
}

// The module the instance `inst` of the design's one top binds, and the module
// its child `f` binds, joined by a slash; empty where either is missing.
std::string BindingsBelow(const ConfigElaboration& run, std::string_view inst) {
  if (run.design == nullptr || run.design->top_modules.size() != 1) return {};
  for (const auto& child : run.design->top_modules[0]->children) {
    if (child.simple_inst_name != inst || child.resolved == nullptr) continue;
    for (const auto& grand : child.resolved->children) {
      if (grand.simple_inst_name != "f" || grand.resolved == nullptr) continue;
      return std::string(child.resolved->name) + "/" +
             std::string(grand.resolved->name);
    }
  }
  return {};
}

// §33.4.1.6: "If the lib.cell to which the use clause refers is a config that
// has the same name as a module/primitive in the same library, then the
// optional :config suffix can be added to the lib.cell to specify the config
// explicitly." With module sub and config sub both in work, `use work.sub`
// binds the module and `use work.sub:config` hands the instance to the config,
// whose rule binding sub.f to m_gate then governs that instance's child alone
// (§33.4.2).
TEST(ConfigHierarchicalRules, ConfigSuffixTellsAConfigFromTheModuleOfItsName) {
  ConfigElaboration run;
  ElaborateUnderConfig(
      "module m; endmodule\n"
      "module m_gate; endmodule\n"
      "module sub; m f(); endmodule\n"
      "module top;\n"
      "  sub a1();\n"
      "  sub a2();\n"
      "endmodule\n"
      "config cfg;\n"
      "  design work.top;\n"
      "  instance top.a1 use work.sub;\n"
      "  instance top.a2 use work.sub:config;\n"
      "endconfig\n"
      "config sub;\n"
      "  design work.sub;\n"
      "  instance sub.f use work.m_gate;\n"
      "endconfig\n",
      run);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(BindingsBelow(run, "a1"), "sub/m");
  EXPECT_EQ(BindingsBelow(run, "a2"), "sub/m_gate");
}

// §33.4.2 (printed page 939): "the rules specified in the config shall
// determine the configuration of all other subinstances" of the instance
// handed to it. cfg5's instance rule names adder.f2 from cfg5's own top, so
// under top.a2 it rebinds f2 alone and under top.a1 nothing.
TEST(ConfigHierarchicalRules, DelegatedInstanceRuleRebindsOnlyItsSubtree) {
  ConfigElaboration run;
  ElaborateUnderConfig(
      "module m; endmodule\n"
      "module m_gate; endmodule\n"
      "module adder; m f(); m f2(); endmodule\n"
      "module top;\n"
      "  adder a1();\n"
      "  adder a2();\n"
      "endmodule\n"
      "config cfg6;\n"
      "  design work.top;\n"
      "  instance top.a2 use work.cfg5:config;\n"
      "endconfig\n"
      "config cfg5;\n"
      "  design work.adder;\n"
      "  instance adder.f use work.m_gate;\n"
      "endconfig\n",
      run);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(BindingsBelow(run, "a1"), "adder/m");
  EXPECT_EQ(BindingsBelow(run, "a2"), "adder/m_gate");
}

// The same for a cell rule of the config handed the instance: `cell m use
// work.m_gate` in cfg5 binds the m beneath top.a2 and leaves top.a1's m alone.
TEST(ConfigHierarchicalRules, DelegatedCellRuleRebindsOnlyItsSubtree) {
  ConfigElaboration run;
  ElaborateUnderConfig(
      "module m; endmodule\n"
      "module m_gate; endmodule\n"
      "module adder; m f(); endmodule\n"
      "module top;\n"
      "  adder a1();\n"
      "  adder a2();\n"
      "endmodule\n"
      "config cfg6;\n"
      "  design work.top;\n"
      "  instance top.a2 use work.cfg5:config;\n"
      "endconfig\n"
      "config cfg5;\n"
      "  design work.adder;\n"
      "  cell m use work.m_gate;\n"
      "endconfig\n",
      run);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(BindingsBelow(run, "a1"), "adder/m");
  EXPECT_EQ(BindingsBelow(run, "a2"), "adder/m_gate");
}

}  // namespace
