#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OrderedPortPreprocessor, OrderedPortConnectionSurvivesPreprocessing) {
  auto r = ParseWithPreprocessor(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(x, y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "child");
  ASSERT_EQ(inst->inst_ports.size(), 2u);
  EXPECT_TRUE(inst->inst_ports[0].first.empty());
  EXPECT_TRUE(inst->inst_ports[1].first.empty());
}

TEST(OrderedPortPreprocessor, OrderedPortWithMacroExpression) {
  auto r = ParseWithPreprocessor(
      "`define WIDTH 8\n"
      "module child(input logic [`WIDTH-1:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [`WIDTH-1:0] x;\n"
      "  child u(x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_ports.size(), 1u);
  EXPECT_TRUE(inst->inst_ports[0].first.empty());
  EXPECT_NE(inst->inst_ports[0].second, nullptr);
}

TEST(OrderedPortPreprocessor, BlankOrderedPortSurvivesPreprocessing) {
  auto r = ParseWithPreprocessor(
      "module child(input logic a, input logic b, input logic c);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, z;\n"
      "  child u(x, , z);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_ports.size(), 3u);
  EXPECT_NE(inst->inst_ports[0].second, nullptr);
  EXPECT_EQ(inst->inst_ports[1].second, nullptr);
  EXPECT_NE(inst->inst_ports[2].second, nullptr);
}

TEST(OrderedPortPreprocessor, MacroExpandedInOrderedPortExpression) {
  auto r = ParseWithPreprocessor(
      "`define INIT_VAL 8'hAB\n"
      "module child(input logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u(`INIT_VAL);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_ports.size(), 1u);
  EXPECT_TRUE(inst->inst_ports[0].first.empty());
  EXPECT_NE(inst->inst_ports[0].second, nullptr);
}

}  // namespace
