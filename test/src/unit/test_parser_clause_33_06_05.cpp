#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(HierarchicalConfigParsing, InstanceRuleUseConfigSetsFlag) {
  auto r = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      instance top.bot use lib1.bot:config;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  ASSERT_GE(r.cu->configs[0]->rules.size(), 2u);
  auto* inst_rule = r.cu->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->use_cell, "bot");
  EXPECT_TRUE(inst_rule->use_config);
}

TEST(HierarchicalConfigParsing, OuterAndInnerConfigsBothParse) {
  auto r = Parse(R"(
    config bot;
      design lib1.bot;
      default liblist lib1 lib2;
    endconfig
    config top;
      design lib1.top;
      instance top.bot use lib1.bot :config;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 2u);
  EXPECT_EQ(r.cu->configs[0]->name, "bot");
  EXPECT_EQ(r.cu->configs[1]->name, "top");

  ASSERT_EQ(r.cu->configs[1]->rules.size(), 1u);
  auto* rule = r.cu->configs[1]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->use_lib, "lib1");
  EXPECT_EQ(rule->use_cell, "bot");
  EXPECT_TRUE(rule->use_config);
}

TEST(HierarchicalConfigParsing, UseConfigSuffixWithoutParams) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use work.sub :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "sub");
  EXPECT_TRUE(rule->use_config);
  EXPECT_EQ(rule->use_params.size(), 0u);
}

}
