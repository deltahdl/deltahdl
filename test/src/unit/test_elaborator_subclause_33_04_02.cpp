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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance 'top.bot.a1' in config 'c' lies within "
                            "subhierarchy 'top.bot' that is delegated to "
                            "another config",
                            5, "33.4.2"));
}

TEST(ConfigHierarchicalRules, TwoRulesOnOneSourceReportAtTwoPlaces) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module top; endmodule\n"
              "config c;\n"
              "  design top;\n"
              "  instance top.bot use lib1.bot:config;\n"
              "  instance top.bot.a1 liblist lib4;\n"
              "endconfig\n"));
  u.ElaborateConfig(0);
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance 'top.a.b' in config 'c' lies within "
                            "subhierarchy 'top.a' that is delegated to another "
                            "config",
                            5, "33.4.2"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance 'top.bot.a1.sub' in config 'c' lies "
                            "within subhierarchy 'top.bot' that is delegated "
                            "to another config",
                            5, "33.4.2"));
}

TEST(ConfigHierarchicalRules,
     DelegatedConfigDesignStatementAndRulesGovernSubtree) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module leaf; endmodule\n"
              "module leaf; endmodule\n"
              "module mid; leaf lf(); endmodule\n"
              "module mid; leaf lf(); endmodule\n"
              "module top; mid m(); endmodule\n"
              "config c;\n"
              "  design top;\n"
              "  default liblist lib1;\n"
              "  instance top.m use lib2.mid:config;\n"
              "endconfig\n"
              "config mid;\n"
              "  design lib2.mid;\n"
              "  default liblist libY;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"libX", "libY", "lib1", "lib2", "libTop"});

  ExpectChainBindsChildAndLeaf(u.ElaborateConfig(0), "mid", "lib2", "libY");
}

TEST(ConfigHierarchicalRules, DelegatedConfigInstanceRuleGovernsSubinstance) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module leaf; endmodule\n"
              "module leaf; endmodule\n"
              "module mid; leaf lf(); endmodule\n"
              "module top; mid m(); endmodule\n"
              "config c;\n"
              "  design top;\n"
              "  instance top.m use lib2.mid:config;\n"
              "endconfig\n"
              "config mid;\n"
              "  design lib2.mid;\n"
              "  instance mid.lf liblist libY;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"libX", "libY", "lib2", "libTop"});

  ExpectChainBindsChildAndLeaf(u.ElaborateConfig(0), "mid", "lib2", "libY");
}

TEST(ConfigHierarchicalRules, DelegatedDesignStatementBindsACellOfAnotherName) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module leaf; endmodule\n"
              "module leaf; endmodule\n"
              "module alt; leaf lf(); endmodule\n"
              "module mid; leaf lf(); endmodule\n"
              "module top; mid m(); endmodule\n"
              "config c;\n"
              "  design top;\n"
              "  default liblist lib1;\n"
              "  instance top.m use lib2.alt:config;\n"
              "endconfig\n"
              "config alt;\n"
              "  design lib2.alt;\n"
              "  default liblist libY;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"libX", "libY", "lib2", "lib1", "libTop"});

  ExpectChainBindsChildAndLeaf(u.ElaborateConfig(0), "alt", "lib2", "libY");
}

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
