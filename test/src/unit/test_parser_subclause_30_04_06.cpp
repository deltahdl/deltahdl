#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(MultiplePathDeclarationParsing, MultipleSourceDestPorts) {
  auto sp = ParseSpecifySingle(
      "module m(input a, b, c, output x, y);\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 12;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  VerifyFullPathPorts(si, {"a", "b", "c"}, {"x", "y"});
}

SpecifyItem* ParseListPath(SpecifyParseResult& sp, const std::string& item) {
  sp = ParseSpecifySingle(
      "module m(input a, b, clk, en, input [3:0] v, output x, y, q, r,\n"
      "         output [3:0] w);\n"
      "  specify\n"
      "    " +
      item +
      "\n"
      "  endspecify\n"
      "endmodule\n");
  if (sp.pr.cu == nullptr) return nullptr;
  EXPECT_FALSE(sp.pr.has_errors);
  return sp.sole_item;
}

TEST(MultiplePathDeclarationParsing, SeveralSourcesToOneDestination) {
  SpecifyParseResult sp;
  auto* si = ParseListPath(sp, "(a, b, en *> x) = 4;");
  ASSERT_NE(si, nullptr);
  VerifyFullPathPorts(si, {"a", "b", "en"}, {"x"});
}

TEST(MultiplePathDeclarationParsing, OneSourceToSeveralDestinations) {
  SpecifyParseResult sp;
  auto* si = ParseListPath(sp, "(a *> x, y, w) = 4;");
  ASSERT_NE(si, nullptr);
  VerifyFullPathPorts(si, {"a"}, {"x", "y", "w"});
}

TEST(MultiplePathDeclarationParsing, ListsMixSelectsWithWholePorts) {
  SpecifyParseResult sp;
  auto* si = ParseListPath(sp, "(a, v[2], v[1:0] *> w[3], x, w[2:0]) = 4;");
  ASSERT_NE(si, nullptr);
  VerifyFullPathPorts(si, {"a", "v", "v"}, {"w", "x", "w"});
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kNone);
  EXPECT_EQ(si->path.src_ports[1].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(si->path.src_ports[2].range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(si->path.dst_ports[2].range_kind, SpecifyRangeKind::kPartSelect);
}

TEST(MultiplePathDeclarationParsing, IfGuardWrapsAPathList) {
  SpecifyParseResult sp;
  auto* si = ParseListPath(sp, "if (en) (a, b *> x, y) = 4;");
  ASSERT_NE(si, nullptr);
  VerifyFullPathPorts(si, {"a", "b"}, {"x", "y"});
  EXPECT_NE(si->path.condition, nullptr);
}

TEST(MultiplePathDeclarationParsing, EdgePathTakesDestinationList) {
  SpecifyParseResult sp;
  auto* si = ParseListPath(sp, "(posedge clk, en *> (q, r : a)) = 4;");
  ASSERT_NE(si, nullptr);
  VerifyFullPathPorts(si, {"clk", "en"}, {"q", "r"});
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_NE(si->path.data_source, nullptr);
}

}  // namespace
