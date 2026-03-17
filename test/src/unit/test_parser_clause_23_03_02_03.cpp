#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ProgramInstantiationGrammar, ProgramInstNamedPortNoParens) {
  auto r = Parse(
      "program my_prog(input logic clk, input logic rst);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

}  // namespace
