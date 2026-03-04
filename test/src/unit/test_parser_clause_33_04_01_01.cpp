#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, ConfigDesignMultipleCells) {
  auto r = Parse(
      "config cfg4;\n"
      "  design work.top lib2.sub cellonly;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->design_cells.size(), 3u);
  EXPECT_EQ(c->design_cells[0].first, "work");
  EXPECT_EQ(c->design_cells[0].second, "top");
  EXPECT_EQ(c->design_cells[1].first, "lib2");
  EXPECT_EQ(c->design_cells[1].second, "sub");

  EXPECT_EQ(c->design_cells[2].first, "");
  EXPECT_EQ(c->design_cells[2].second, "cellonly");
}

TEST_F(ConfigTest, DesignStatementParsed) {
  auto* unit = Parse(R"(
    config cfg;
      design lib1.top;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  EXPECT_EQ(cfg->name, "cfg");
  ASSERT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_EQ(cfg->design_cells[0].first, "lib1");
  EXPECT_EQ(cfg->design_cells[0].second, "top");
}

TEST_F(ConfigTest, DesignStatementNoLib) {
  auto* unit = Parse(R"(
    config cfg;
      design top;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_TRUE(cfg->design_cells[0].first.empty());
  EXPECT_EQ(cfg->design_cells[0].second, "top");
}

TEST_F(ConfigTest, DesignStatementMultipleTopCells) {
  auto* unit = Parse(R"(
    config cfg;
      design lib1.top1 lib2.top2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->design_cells.size(), 2u);
  EXPECT_EQ(cfg->design_cells[0].first, "lib1");
  EXPECT_EQ(cfg->design_cells[0].second, "top1");
  EXPECT_EQ(cfg->design_cells[1].first, "lib2");
  EXPECT_EQ(cfg->design_cells[1].second, "top2");
}

}
