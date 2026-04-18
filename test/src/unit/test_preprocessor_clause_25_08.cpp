// §25.8

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParameterizedInterfaces, ParametersConstantsVariables) {
  auto r = ParseWithPreprocessor(
      "interface ifc #(parameter WIDTH = 8);\n"
      "  localparam DEPTH = 16;\n"
      "  logic [WIDTH-1:0] data;\n"
      "  wire valid;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 2u);
}

TEST(ParameterizedInterfaces, ParameterDefaultFromMacro) {
  auto r = ParseWithPreprocessor(
      "`define DEFW 12\n"
      "interface ifc #(parameter int WIDTH = `DEFW);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->params.size(), 1u);
}

TEST(ParameterizedInterfaces, InstanceOverrideFromMacro) {
  auto r = ParseWithPreprocessor(
      "`define OVR 32\n"
      "interface ifc #(parameter int WIDTH = 8);\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.WIDTH(`OVR)) u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* inst = r.cu->modules[0]->items[0];
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_params[0].first, "WIDTH");
}

}  // namespace
