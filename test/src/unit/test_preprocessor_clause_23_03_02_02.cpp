#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleInstantiation, NamedPortConnections) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  logic in1, in2, sel;\n"
      "  wire out1;\n"
      "  mux2to1 m1 (.a(in1), .b(in2), .sel(sel), .y(out1));\n"
      "endmodule\n"
      "module mux2to1 (input wire a, b, sel, output logic y);\n"
      "  not g1 (sel_n, sel);\n"
      "  and g2 (a_s, a, sel_n);\n"
      "  and g3 (b_s, b, sel);\n"
      "  or  g4 (y, a_s, b_s);\n"
      "endmodule : mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "top");
  EXPECT_EQ(r.cu->modules[1]->name, "mux2to1");

  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "mux2to1");
  EXPECT_EQ(inst->inst_name, "m1");
  EXPECT_EQ(inst->inst_ports.size(), 4u);

  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[1]->items, ModuleItemKind::kGateInst), 4);
}

TEST(ModuleInstantiation, NamedPortWithMacroExpression) {
  auto r = ParseWithPreprocessor(
      "`define INIT_VAL 8'hAB\n"
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] y;\n"
      "  child u(.a(`INIT_VAL), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_ports.size(), 2u);
  EXPECT_EQ(inst->inst_ports[0].first, "a");
  EXPECT_NE(inst->inst_ports[0].second, nullptr);
  EXPECT_EQ(inst->inst_ports[1].first, "b");
}

TEST(ModuleInstantiation, EmptyNamedPortSurvivesPreprocessing) {
  auto r = ParseWithPreprocessor(
      "module child(input logic a, output logic b);\n"
      "  assign b = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  logic y;\n"
      "  child u(.a(), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_ports.size(), 2u);
  EXPECT_EQ(inst->inst_ports[0].first, "a");
  EXPECT_EQ(inst->inst_ports[0].second, nullptr);
  EXPECT_EQ(inst->inst_ports[1].first, "b");
  EXPECT_NE(inst->inst_ports[1].second, nullptr);
}

}  // namespace
