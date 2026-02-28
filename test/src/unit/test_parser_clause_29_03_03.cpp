// §29.3.3: Sequential UDP initial statement

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- udp_declaration: sequential with initial statement ---
TEST(ParserAnnexA051, SequentialWithInitial) {
  auto r = Parse(
      "primitive srff(output reg q, input s, input r);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    1 0 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

}  // namespace
