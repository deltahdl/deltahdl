#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

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

// §30.4.6: a multi-path declaration always records a full connection.
TEST(MultiplePathDeclarationParsing, MultiPathIsFullConnection) {
  auto sp = ParseSpecifySingle(
      "module m(input a, b, output x, y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.src_ports.size(), 2u);
  EXPECT_EQ(si->path.dst_ports.size(), 2u);
}

// §30.4.6: source and destination lists may mix scalars and vectors of any
// size.
TEST(MultiplePathDeclarationParsing, MixedScalarVectorListsParse) {
  auto sp = ParseSpecifySingle(
      "module m(input a, input [3:0] b, input [7:0] c,\n"
      "         output x, output [15:0] y);\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 4;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.src_ports.size(), 3u);
  EXPECT_EQ(si->path.dst_ports.size(), 2u);
}

}  // namespace
