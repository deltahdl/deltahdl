// §28.6

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(EnableGates, TooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 b1(out, in, en, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// --- Multiple instances with mixed named/unnamed across all types ---
TEST(EnableGates, MultipleInstancesMixed) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 b1(o1, a, en), (o2, b, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->gate_inst_name, "b1");
  EXPECT_TRUE(gates[1]->gate_inst_name.empty());
}

}  // namespace
