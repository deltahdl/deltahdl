// §33.4.3: Setting parameters in configurations

#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// §33.4.3 Config with parameter override
// =============================================================================
TEST_F(ConfigTest, UseClauseWithParams) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      instance top.u1 use lib.adder #(.WIDTH(16), .DEPTH(4));
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->use_lib, "lib");
  EXPECT_EQ(rule->use_cell, "adder");
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "WIDTH");
  EXPECT_EQ(rule->use_params[1].first, "DEPTH");
}

TEST_F(ConfigTest, LocalparamInConfig) {
  auto* unit = Parse(R"(
    config cfg;
      localparam W = 32;
      design lib.top;
      default liblist lib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->local_params.size(), 1u);
  EXPECT_EQ(cfg->local_params[0].first, "W");
  EXPECT_NE(cfg->local_params[0].second, nullptr);
}

}  // namespace
