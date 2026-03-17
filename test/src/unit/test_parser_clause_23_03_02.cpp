#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(InterfaceInstantiationGrammar, InterfaceInstEmptyParam) {
  auto r = Parse("module m; my_if #() u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_TRUE(item->inst_params.empty());
}

TEST(ProgramInstantiationGrammar, ProgramInstEmptyParam) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog #() u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_TRUE(item->inst_params.empty());
}

}  // namespace
