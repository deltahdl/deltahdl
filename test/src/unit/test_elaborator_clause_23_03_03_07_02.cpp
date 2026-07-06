
#include "fixture_elaborator.h"

using namespace delta;

// §23.3.3.7.2: an interconnect net on a gate/UDP terminal is retyped to a plain
// wire during elaboration. The rule draws no distinction between gate kinds,
// instance naming, or whether a sibling terminal is a literal or a real net, so
// one representative per rule-relevant input form is kept here: gate input,
// gate output, a single-terminal source primitive, a gate carrying interconnect
// on every terminal (exercising the terminal loop when no sibling is
// non-interconnect), plus the corresponding UDP input/output/all-interconnect
// cases (a distinct elaboration path from gate instances).

namespace {

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

TEST(InterconnectPrimitiveTerminalElaboration, InterconnectOnPullupNoError) {
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

TEST(InterconnectPrimitiveTerminalElaboration, InterconnectOnUdpInputNoError) {
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

TEST(InterconnectPrimitiveTerminalElaboration, InterconnectOnUdpOutputNoError) {
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
