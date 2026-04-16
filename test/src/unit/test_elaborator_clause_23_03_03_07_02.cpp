
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- Interconnect net on built-in primitive gate input terminal ---

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnAndGateInputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  and (y, ic, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnOrGateInputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  or (y, ic, 1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnNandGateInputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  nand (y, ic, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnNorGateInputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  nor (y, ic, 1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnXorGateInputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  xor (y, ic, 1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnXnorGateInputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  xnor (y, ic, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnBufGateInputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  buf (y, ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnNotGateInputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  not (y, ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Interconnect net on built-in primitive gate output terminal ---

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnAndGateOutputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire a, b;\n"
      "  and (ic, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnBufGateOutputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire a;\n"
      "  buf (ic, a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnPullupNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  pullup (ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnPulldownNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  pulldown (ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- All gate terminals as interconnect ---

TEST(InterconnectPrimitiveTerminalElaboration,
     AllTerminalsInterconnectOnAndGateNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic_a, ic_b, ic_y;\n"
      "  and (ic_y, ic_a, ic_b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Mixed interconnect and wire terminals ---

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectMixedWithWireOnGateNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire a, y;\n"
      "  and (y, ic, a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Named gate instance with interconnect terminal ---

TEST(InterconnectPrimitiveTerminalElaboration,
     NamedGateInstanceWithInterconnectNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  and g1 (y, ic, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Interconnect net on UDP input terminal ---

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnUdpInputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  my_udp u(y, ic, 1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Interconnect net on UDP output terminal ---

TEST(InterconnectPrimitiveTerminalElaboration,
     InterconnectOnUdpOutputNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  wire a, b;\n"
      "  my_udp u(ic, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- All UDP terminals as interconnect ---

TEST(InterconnectPrimitiveTerminalElaboration,
     AllTerminalsInterconnectOnUdpNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  interconnect ic_y, ic_a, ic_b;\n"
      "  my_udp u(ic_y, ic_a, ic_b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
