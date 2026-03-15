// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, ModuleWithGenerateIf) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter int P = 1;\n"
              "  if (P) begin : gen\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, ModuleWithSpecifyBlock) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n"
      "    (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_specify = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) has_specify = true;
  }
  EXPECT_TRUE(has_specify);
}

TEST(DesignBuildingBlockParsing, Mux2to1Example) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule: mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "mux2to1");
  EXPECT_FALSE(r.cu->modules[0]->ports.empty());
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

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
