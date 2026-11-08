#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

uint32_t PortWidthByName(const RtlirModule* mod, std::string_view name) {
  for (const auto& p : mod->ports) {
    if (p.name == name) return p.width;
  }
  return 0;
}

TEST(ParameterizedModulePorts, NonAnsiPortRangeDerivesWidthFromParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module generic_fifo (in, out);\n"
      "  parameter MSB = 3, LSB = 0, DEPTH = 4;\n"
      "  input  [MSB:LSB] in;\n"
      "  output [MSB:LSB] out;\n"
      "endmodule\n",
      f, "generic_fifo");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* m = design->top_modules[0];
  EXPECT_EQ(PortWidthByName(m, "in"), 4u);
  EXPECT_EQ(PortWidthByName(m, "out"), 4u);
}

TEST(ParameterizedModulePorts, AnsiPortRangeDerivesWidthFromParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module generic_fifo\n"
      "  #(parameter MSB = 3, LSB = 0, DEPTH = 4)\n"
      "   (input [MSB:LSB] in, output [MSB:LSB] out);\n"
      "endmodule\n",
      f, "generic_fifo");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* m = design->top_modules[0];
  EXPECT_EQ(PortWidthByName(m, "in"), 4u);
  EXPECT_EQ(PortWidthByName(m, "out"), 4u);
}

TEST(ParameterizedModulePorts, PerInstanceOverrideCustomizesPortWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module ch #(parameter W = 4)(input [W-1:0] in);\n"
      "endmodule\n"
      "module top;\n"
      "  ch #(8) a();\n"
      "  ch b();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& children = design->top_modules[0]->children;
  ASSERT_EQ(children.size(), 2u);
  auto* a = children[0].resolved;
  auto* b = children[1].resolved;
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(PortWidthByName(a, "in"), 8u);
  EXPECT_EQ(PortWidthByName(b, "in"), 4u);
}

TEST(ParameterizedModulePorts, NamedParameterOverrideCustomizesPortWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module ch #(parameter W = 4)(input [W-1:0] in);\n"
      "endmodule\n"
      "module top;\n"
      "  ch #(.W(8)) a();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& children = design->top_modules[0]->children;
  ASSERT_EQ(children.size(), 1u);
  auto* a = children[0].resolved;
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(PortWidthByName(a, "in"), 8u);
}

TEST(ParameterizedModulePorts, AnsiLocalparamInPortListSizesPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module generic_decoder\n"
      "  #(parameter num_code_bits = 3,\n"
      "    localparam num_out_bits = 1 << num_code_bits)\n"
      "   (input [num_code_bits-1:0] A, output reg [num_out_bits-1:0] Y);\n"
      "endmodule\n",
      f, "generic_decoder");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* m = design->top_modules[0];
  EXPECT_EQ(PortWidthByName(m, "A"), 3u);
  EXPECT_EQ(PortWidthByName(m, "Y"), 8u);
}

TEST(ParameterizedModulePorts, DerivedLocalparamPortRecomputesUnderOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module generic_decoder\n"
      "  #(parameter num_code_bits = 3,\n"
      "    localparam num_out_bits = 1 << num_code_bits)\n"
      "   (input [num_code_bits-1:0] A, output reg [num_out_bits-1:0] Y);\n"
      "endmodule\n"
      "module top;\n"
      "  generic_decoder #(4) d();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& children = design->top_modules[0]->children;
  ASSERT_EQ(children.size(), 1u);
  auto* d = children[0].resolved;
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(PortWidthByName(d, "A"), 4u);
  EXPECT_EQ(PortWidthByName(d, "Y"), 16u);
}

}  // namespace
