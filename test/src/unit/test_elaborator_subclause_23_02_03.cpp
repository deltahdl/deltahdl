#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §23.2.3: port declarations can be based on parameter declarations. The rule
// applies at elaboration, where the parameter values are resolved (default or
// per-instance override) and the port packed-range constant expressions are
// folded against that parameter scope to give each port its width. Look a port
// up by name so the assertions do not depend on declaration order.
uint32_t PortWidthByName(const RtlirModule* mod, std::string_view name) {
  for (const auto& p : mod->ports) {
    if (p.name == name) return p.width;
  }
  return 0;
}

// Example 1 (non-ANSI style header): the ports in/out are declared with the
// packed range [MSB:LSB], whose bounds are module parameters. With the declared
// defaults (MSB=3, LSB=0) the elaborated port width is MSB-LSB+1 = 4. A width
// of 4 (not the scalar default of 1) witnesses that the parameter values
// reached the port range.
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

// Example 2 (ANSI style header): the same parameter-based port ranges declared
// in an ANSI parameter_port_list. The rule is header-style independent, so the
// elaborated widths match the non-ANSI case.
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

// The heart of §23.2.3: parameter redefinition per instance customizes each
// instance's port characteristics. Two instances of the same parameterized
// module — one overriding the width parameter (§23.10 ordered redefinition),
// one at the default — resolve to distinct port widths. The contrast between
// the two instances is the witness that the port width tracks the per-instance
// parameter value rather than a fixed declaration-time width.
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

// Same per-instance customization rule, reached through the named parameter
// redefinition form (§23.10 by-name assignment) instead of the ordered form
// used above. The override binds W to 8 by name, and the port packed range
// [W-1:0] resolves to that value, so the instance's port is 8 bits wide.
// Driving the rule through the alternative redefinition syntax exercises a
// distinct override code path while observing the same §23.2.3 port-sizing
// effect.
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

// Example 3: a localparam in the ANSI parameter_port_list is defined from a
// preceding parameter (num_out_bits = 1 << num_code_bits) and sizes a port. At
// the declared defaults, port A takes num_code_bits (=3) and port Y takes
// num_out_bits (=1<<3=8). This exercises a port range based on a derived
// localparam, not just a directly declared parameter.
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

// Example 3 under a per-instance override: overriding num_code_bits to 4
// recomputes both the directly parameterized port (A -> 4) and the port sized
// by the derived localparam (Y -> 1<<4 = 16). The override propagating through
// the localparam into the port width is the strongest form of §23.2.3's
// per-instance customization.
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
