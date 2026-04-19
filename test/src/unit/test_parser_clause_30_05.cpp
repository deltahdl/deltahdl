#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SpecifyPathDelayParsing, PathDelayValueBare) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(SpecifyPathDelayParsing, PathDelayValueParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(SpecifyPathDelayParsing, PathDelayWithSpecparam) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tDelay = 10;\n"
      "    (a => b) = tDelay;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_GE(spec->specify_items.size(), 2u);
  auto* path_item = spec->specify_items[1];
  EXPECT_EQ(path_item->kind, SpecifyItemKind::kPathDecl);
  ASSERT_EQ(path_item->path.delays.size(), 1u);
}

TEST(SpecifyPathDelayParsing, ListOfPathDelayExpr2) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (3, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 2u);
}

TEST(SpecifyPathDelayParsing, ListOfPathDelayExpr3) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (2, 3, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 3u);
}

TEST(SpecifyPathDelayParsing, ListOfPathDelayExpr6) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 6u);
}

TEST(SpecifyPathDelayParsing, ListOfPathDelayExpr12) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 12u);
}

TEST(SpecifyPathDelayParsing, SpecparamMinTypMax) {
  EXPECT_TRUE(
      ParseOk("module m(input a, output b);\n"
              "  specify\n"
              "    specparam tPLH = 3:5:7;\n"
              "    (a => b) = tPLH;\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(SpecifyPathDelayParsing, PathDelayExprMinTypMaxBare) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
  EXPECT_EQ(si->path.delays[0]->kind, ExprKind::kMinTypMax);
}

TEST(SpecifyPathDelayParsing, PathDelayExprMinTypMaxParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1:2:3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
  EXPECT_EQ(si->path.delays[0]->kind, ExprKind::kMinTypMax);
}

TEST(SpecifyPathDelayParsing, PathDelayExprMinTypMax2) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 2u);
  EXPECT_EQ(si->path.delays[0]->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(si->path.delays[1]->kind, ExprKind::kMinTypMax);
}

TEST(SpecifyPathDelayParsing, PathDelayExprMinTypMax3) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1:2:3, 4:5:6, 7:8:9);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 3u);
  for (int i = 0; i < 3; ++i) {
    EXPECT_EQ(si->path.delays[i]->kind, ExprKind::kMinTypMax);
  }
}

TEST(SpecifyPathDelayParsing, PathDelayExprMinTypMax6) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1:2:3, 4:5:6, 7:8:9, 10:11:12, 13:14:15, 16:17:18);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 6u);
  for (int i = 0; i < 6; ++i) {
    EXPECT_EQ(si->path.delays[i]->kind, ExprKind::kMinTypMax);
  }
}

TEST(SpecifyPathDelayParsing, PathDelayExprMinTypMax12) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1:2:3, 4:5:6, 7:8:9, 10:11:12, 13:14:15, 16:17:18,\n"
      "               19:20:21, 22:23:24, 25:26:27, 28:29:30, 31:32:33, "
      "34:35:36);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 12u);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(si->path.delays[i]->kind, ExprKind::kMinTypMax);
  }
}

TEST(SpecifyPathDelayParsing, PathDelayRiseFallSpecparams) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 3;\n"
      "    specparam tFall = 5;\n"
      "    (a => b) = (tRise, tFall);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SpecifyPathDelayParsing, InvalidDelayCount4) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathDelayParsing, InvalidDelayCount5) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathDelayParsing, InvalidDelayCount7) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5, 6, 7);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathDelayParsing, SixDelaysEdgeSensitive) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => q) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  ASSERT_EQ(si->path.delays.size(), 6u);
}

TEST(SpecifyPathDelayParsing, SixDelaysConditionalPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (a => b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  ASSERT_EQ(si->path.delays.size(), 6u);
}

TEST(SpecifyPathDelayParsing, ErrorEmptyDelayList) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = ();\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
