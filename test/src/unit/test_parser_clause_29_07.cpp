// §29.7: Sequential UDP initialization

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- udp_declaration: sequential with initial value 1 ---
TEST(ParserAnnexA051, SequentialInitialOne) {
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

// ---------------------------------------------------------------------------
// Production 5: udp_initial_statement ::= initial output_port_identifier =
//               init_val ;
// ---------------------------------------------------------------------------
// Initial statement parsed correctly
TEST(ParserAnnexA053, InitStmt_Parsed) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

}  // namespace
