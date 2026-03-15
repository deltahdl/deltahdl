// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, ModuleWithMixedContents) {
  EXPECT_TRUE(ParseOk(
      "module m #(parameter int W = 8) (input logic clk, output logic [W-1:0] "
      "q);\n"
      "  typedef logic [W-1:0] data_t;\n"
      "  wire [W-1:0] net;\n"
      "  logic [W-1:0] var;\n"
      "  localparam int HALF = W / 2;\n"
      "  function automatic data_t invert(data_t d); return ~d; endfunction\n"
      "  assign net = var;\n"
      "  always_comb var = invert(q);\n"
      "  always_ff @(posedge clk) q <= net;\n"
      "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, MultipleModulesInOneCU) {
  auto r = Parse(
      "module a; endmodule\nmodule b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(DesignBuildingBlockParsing, MismatchedEndKeywordIsError) {
  EXPECT_FALSE(ParseOk("module m; endprogram"));
}

TEST(DesignBuildingBlockParsing, UnclosedModuleIsError) {
  EXPECT_FALSE(ParseOk("module m;"));
}

}  // namespace
