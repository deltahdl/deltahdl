#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ProgramInstantiationGrammar, ProgramInstWithNamedParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(.W(16)) u0(.data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

}  // namespace
