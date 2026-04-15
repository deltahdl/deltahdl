#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(WildcardPortConnectionPreprocessing, WildcardSurvivesPreprocessing) {
  auto r = ParseWithPreprocessor(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_wildcard);
  EXPECT_TRUE(inst->inst_ports.empty());
}

TEST(WildcardPortConnectionPreprocessing, WildcardMixedWithMacroInOverride) {
  auto r = ParseWithPreprocessor(
      "`define CLK sys_clk\n"
      "module child(input logic clk, input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic sys_clk, a, b;\n"
      "  child u0(.clk(`CLK), .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_wildcard);
  ASSERT_EQ(inst->inst_ports.size(), 1u);
  EXPECT_EQ(inst->inst_ports[0].first, "clk");
}

TEST(WildcardPortConnectionPreprocessing, WildcardWithConditionalCompilation) {
  auto r = ParseWithPreprocessor(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "`ifdef USE_NAMED\n"
      "  child u0(.a(a), .b(b));\n"
      "`else\n"
      "  child u0(.*);\n"
      "`endif\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_wildcard);
}

}  // namespace
