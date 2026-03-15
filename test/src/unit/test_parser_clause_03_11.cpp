// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, ModuleInstantiatesInterface) {
  EXPECT_TRUE(
      ParseOk("interface ifc; logic req; endinterface\n"
              "module m;\n"
              "  ifc u0();\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, PortConnections) {
  auto r = Parse(
      "module sub(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  sub u0(.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst =
      FindItemByKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_FALSE(inst->inst_ports.empty());
}

TEST(DesignBuildingBlockParsing, TopMux2to1Example) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  not g1 (sel_n, sel);\n"
      "  and g2 (a_s, a, sel_n);\n"
      "  and g3 (b_s, b, sel);\n"
      "  or  g4 (y, a_s, b_s);\n"
      "endmodule: mux2to1\n"
      "module top;\n"
      "  logic in1, in2, select;\n"
      "  wire out1;\n"
      "  mux2to1 m1 (.a(in1), .b(in2), .sel(select), .y(out1));\n"
      "endmodule: top\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[1]->name, "top");
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst));
}

TEST(DesignBuildingBlockParsing, MultipleLevelsOfHierarchy) {
  EXPECT_TRUE(
      ParseOk("module leaf; endmodule\n"
              "module mid; leaf u0(); endmodule\n"
              "module top; mid u0(); endmodule\n"));
}

TEST(DesignBuildingBlockParsing, MultipleTopLevelModules) {
  auto r = Parse(
      "module top_a; endmodule\n"
      "module top_b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 2u);
}

}  // namespace
