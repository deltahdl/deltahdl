// §9.4.2: Event control

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// edge_identifier ::= posedge | negedge | edge
// ---------------------------------------------------------------------------
// §9.4.2: all three edge identifiers parsed correctly
TEST(ParserA605, EdgeIdentifiers) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge a or negedge b or edge c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 3u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kEdge);
}

}  // namespace
