
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectInternalWireNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectInternalWandNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectInternalWorNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wor a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectInternalTriregNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trireg a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectInternalTri0NoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectInternalTri1NoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri1 a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectInternalUwireNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectInternalSupply0NoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout supply0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectInternalSupply1NoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout supply1 a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     InternalInterconnectExternalWireNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout interconnect a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     InternalInterconnectExternalWandNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout interconnect a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     BothInterconnectIllegalAtEndOfElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout interconnect a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     PositionalBothInterconnectIllegalAtEndOfElaboration) {
  // Same end-of-elaboration illegality as the named case, reached through a
  // positional port connection: when both the internal port and the external
  // connection are interconnect, the merged simulated net would still be an
  // interconnect net, which is not permitted.
  ElabFixture f;
  ElaborateSrc(
      "module child(inout interconnect a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(ic);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     PositionalConnectionWithExternalInterconnectNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     InputPortWithExternalInterconnectNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     OutputPortWithExternalInterconnectNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire a);\n"
      "  assign a = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     InterconnectConnectedToMultipleDissimilarChildPorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dut1(inout wire w);\n"
      "  assign w = 1;\n"
      "endmodule\n"
      "module dut2(inout wand w);\n"
      "  assign w = 0;\n"
      "endmodule\n"
      "module netlist;\n"
      "  interconnect iwire;\n"
      "  dut1 child1(iwire);\n"
      "  dut2 child2(iwire);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
