#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §30.4: "A module path shall be defined inside a specify block as a connection
// between a source signal and a destination signal." A simple path written
// inside a specify block yields a path declaration whose source and destination
// terminals are the paired signals.
TEST(ModulePathDeclParsing, PathInsideSpecifyPairsSourceAndDestination) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* si = spec->specify_items[0];
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
}

// §30.4: the module path "shall be defined inside a specify block." A path
// declaration written directly as a module item, with no enclosing specify
// block, is not a valid module_or_generate_item and must be rejected.
TEST(ModulePathDeclParsing, PathOutsideSpecifyBlockRejected) {
  auto r = Parse(
      "module m;\n"
      "  (a => b) = 5;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §30.4: "A module path may be described as a simple path, an edge-sensitive
// path, or a state-dependent path." All three forms parse as path declarations
// within one specify block, distinguished by their edge and enabling-condition
// attributes.
TEST(ModulePathDeclParsing, SimpleEdgeAndStateDependentPathsRecognized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    (posedge clk => q) = 5;\n"
      "    if (en) (c => d) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  // Simple path: neither a source edge nor an enabling condition.
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[0]->path.edge, SpecifyEdge::kNone);
  EXPECT_EQ(spec->specify_items[0]->path.condition, nullptr);
  // Edge-sensitive path: a source edge identifier is present.
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[1]->path.edge, SpecifyEdge::kPosedge);
  // State-dependent path: an enabling condition is present.
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_NE(spec->specify_items[2]->path.condition, nullptr);
}

}  // namespace
