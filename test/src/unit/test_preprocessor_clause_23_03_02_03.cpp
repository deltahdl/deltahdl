#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ImplicitNamedPortConnectionPreprocessing, ImplicitConnectionSurvivesPreprocessing) {
  auto r = ParseWithPreprocessor(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(.a, .b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_ports.size(), 2u);
  EXPECT_EQ(inst->inst_ports[0].first, "a");
  EXPECT_EQ(inst->inst_ports[1].first, "b");
}

TEST(ImplicitNamedPortConnectionPreprocessing, ImplicitPortMixedWithMacroInExplicitPort) {
  auto r = ParseWithPreprocessor(
      "`define VAL 8'hFF\n"
      "module child(input logic [7:0] a, input logic [7:0] b,\n"
      "             output logic [7:0] c);\n"
      "  assign c = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, c;\n"
      "  child u0(.a, .b(`VAL), .c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_ports.size(), 3u);
  EXPECT_EQ(inst->inst_ports[0].first, "a");
  EXPECT_EQ(inst->inst_ports[1].first, "b");
  EXPECT_NE(inst->inst_ports[1].second, nullptr);
  EXPECT_EQ(inst->inst_ports[2].first, "c");
}

}  // namespace
