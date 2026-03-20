#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(UdpInstantiationParsing, UdpInstBasic) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv u1(y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->inst_module, "inv");
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_EQ(insts[0]->gate_terminals.size(), 2u);
}

TEST(UdpInstantiationParsing, UdpInstUnnamed) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv (y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_TRUE(insts[0]->gate_inst_name.empty());
  EXPECT_EQ(insts[0]->gate_terminals.size(), 2u);
}

TEST(UdpInstantiationParsing, UdpInstMultipleInputs) {
  auto r = Parse(
      "primitive mux(output out, input a, b, sel);\n"
      "  table\n"
      "    0 ? 0 : 0;\n"
      "    1 ? 0 : 1;\n"
      "    ? 0 1 : 0;\n"
      "    ? 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a, b, s;\n"
      "  mux u1(y, a, b, s);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->gate_terminals.size(), 4u);
}

TEST(UdpInstantiationParsing, UdpInstMultipleInstances) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y1, y2, a, b;\n"
      "  inv u1(y1, a), u2(y2, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 2u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_EQ(insts[1]->gate_inst_name, "u2");
}

TEST(UdpInstantiationParsing, UdpInstWithDriveStrength) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv (strong0, weak1) u1(y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->drive_strength0, 4u);
  EXPECT_EQ(insts[0]->drive_strength1, 2u);
}

TEST(UdpInstantiationParsing, UdpInstWithDelaySingle) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv #5 u1(y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  ASSERT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay->int_val, 5u);
  EXPECT_EQ(insts[0]->gate_delay_fall, nullptr);
}

TEST(UdpInstantiationParsing, UdpInstWithDelayTwo) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv #(3, 7) u1(y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  ASSERT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay->int_val, 3u);
  ASSERT_NE(insts[0]->gate_delay_fall, nullptr);
  EXPECT_EQ(insts[0]->gate_delay_fall->int_val, 7u);
}

TEST(UdpInstantiationParsing, UdpInstStrengthAndDelay) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv (pull0, pull1) #10 u1(y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->drive_strength0, 3u);
  EXPECT_EQ(insts[0]->drive_strength1, 3u);
  ASSERT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay->int_val, 10u);
}

TEST(UdpInstantiationParsing, UdpInstWithInstanceArray) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire [3:0] y, a;\n"
      "  inv u1 [3:0] (y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_NE(insts[0]->inst_range_left, nullptr);
  EXPECT_NE(insts[0]->inst_range_right, nullptr);
}

TEST(UdpInstantiationParsing, UdpInstNoStrengthNoDelay) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv u1(y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->drive_strength0, 0u);
  EXPECT_EQ(insts[0]->drive_strength1, 0u);
  EXPECT_EQ(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay_fall, nullptr);
}

TEST(UdpInstantiationParsing, UdpInstStrengthSharedAcrossInstances) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y1, y2, a, b;\n"
      "  inv (supply0, supply1) u1(y1, a), u2(y2, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 2u);
  EXPECT_EQ(insts[0]->drive_strength0, 5u);
  EXPECT_EQ(insts[0]->drive_strength1, 5u);
  EXPECT_EQ(insts[1]->drive_strength0, 5u);
  EXPECT_EQ(insts[1]->drive_strength1, 5u);
}

TEST(UdpInstantiationParsing, UdpInstSequential) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire q, d, clk;\n"
      "  dff u1(q, d, clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->inst_module, "dff");
  EXPECT_EQ(insts[0]->gate_terminals.size(), 3u);
}

TEST(UdpInstantiationParsing, UdpInst_BasicNamed) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp u1(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->inst_module, "my_udp");
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_EQ(insts[0]->gate_terminals.size(), 3u);
}

TEST(UdpInstantiationParsing, UdpInst_Unnamed) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp (out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->inst_module, "my_udp");
  EXPECT_TRUE(insts[0]->gate_inst_name.empty());
  EXPECT_EQ(insts[0]->gate_terminals.size(), 3u);
}

TEST(UdpInstantiationParsing, UdpInst_DriveStrength) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp (strong0, pull1) u1(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_NE(insts[0]->drive_strength0, 0);
  EXPECT_NE(insts[0]->drive_strength1, 0);
}

TEST(UdpInstantiationParsing, UdpInst_DriveStrengthReversed) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp (pull1, strong0) u1(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_NE(insts[0]->drive_strength0, 0);
  EXPECT_NE(insts[0]->drive_strength1, 0);
}

TEST(UdpInstantiationParsing, UdpInst_DelaySingle) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp #5 u1(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay_fall, nullptr);
  EXPECT_EQ(insts[0]->gate_delay_decay, nullptr);
}

TEST(UdpInstantiationParsing, UdpInst_DelayRiseFall) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp #(3, 5) u1(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_NE(insts[0]->gate_delay_fall, nullptr);
  EXPECT_EQ(insts[0]->gate_delay_decay, nullptr);
}

TEST(UdpInstantiationParsing, UdpInst_StrengthAndDelay) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp (weak0, weak1) #7 u1(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_NE(insts[0]->drive_strength0, 0);
  EXPECT_NE(insts[0]->drive_strength1, 0);
  EXPECT_NE(insts[0]->gate_delay, nullptr);
}

TEST(UdpInstantiationParsing, UdpInst_MultipleInstances) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp u1(o1, i1, i2), u2(o2, i3, i4);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 2u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_EQ(insts[1]->gate_inst_name, "u2");
}

TEST(UdpInstantiationParsing, UdpInst_MultipleWithStrengthDelay) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp (strong0, strong1) #10 u1(o1, i1, i2), u2(o2, i3, i4);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 2u);

  EXPECT_NE(insts[0]->drive_strength0, 0);
  EXPECT_NE(insts[1]->drive_strength0, 0);
  EXPECT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_NE(insts[1]->gate_delay, nullptr);
}

TEST(UdpInstantiationParsing, UdpInst_InstanceArray) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp u1[3:0](out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_NE(insts[0]->inst_range_left, nullptr);
  EXPECT_NE(insts[0]->inst_range_right, nullptr);
}

TEST(UdpInstantiationParsing, UdpInst_SingleInput) {
  auto r = Parse(
      "primitive my_buf(output y, input a);\n"
      "  table\n"
      "    0 : 0 ;\n"
      "    1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_buf u1(out, in1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->gate_terminals.size(), 2u);
}

TEST(UdpInstantiationParsing, UdpInst_ManyInputs) {
  auto r = Parse(
      "primitive my_gate(output y, input a, input b, input c, input d);\n"
      "  table\n"
      "    0 0 0 0 : 0 ;\n"
      "    1 1 1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_gate u1(out, in1, in2, in3, in4);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->gate_terminals.size(), 5u);
}

TEST(UdpInstantiationParsing, UdpInst_WithAttributes) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  (* synthesis *) my_udp u1(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_FALSE(insts[0]->attrs.empty());
}

TEST(UdpInstantiationParsing, UdpInstance) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  wire a, b;\n"
      "  inv u1(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->inst_module, "inv");
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
}

TEST(UdpInstantiationParsing, UdpInstanceInModule) {
  auto r = Parse(
      "primitive udp_and (output out, input a, b);\n"
      "  table 0 0 : 0; 0 1 : 0; 1 0 : 0; 1 1 : 1; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire a, b, y;\n"
      "  udp_and u1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kUdpInst));
}

TEST(UdpInstantiationParsing, BuiltInAndUdpCoexist) {
  auto r = Parse(
      "primitive udp_inv (output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire a, b, y1, y2;\n"
      "  and g1(y1, a, b);\n"
      "  udp_inv u1(y2, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst));
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kUdpInst));
}

TEST(UdpInstantiationParsing, UdpInst_ExternUdp) {
  auto r = Parse(
      "extern primitive my_udp(output y, input a, input b);\n"
      "module m;\n"
      "  my_udp u1(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->inst_module, "my_udp");
}

// --- error conditions ---

TEST(UdpInstantiationParsing, SingleTerminalError) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  inv u1(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  if (!insts.empty()) {
    EXPECT_EQ(insts[0]->gate_terminals.size(), 1u);
  }
}

// --- edge cases ---

TEST(UdpInstantiationParsing, MultipleUnnamedInstances) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y1, y2, a, b;\n"
      "  inv (y1, a), (y2, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 2u);
  EXPECT_TRUE(insts[0]->gate_inst_name.empty());
  EXPECT_TRUE(insts[1]->gate_inst_name.empty());
}

TEST(UdpInstantiationParsing, DelaySharedAcrossInstances) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y1, y2, a, b;\n"
      "  inv #5 u1(y1, a), u2(y2, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 2u);
  EXPECT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_NE(insts[1]->gate_delay, nullptr);
}

TEST(UdpInstantiationParsing, ExpressionTerminals) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire [3:0] y, a;\n"
      "  inv u1(y[0], a[0]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->gate_terminals.size(), 2u);
}

TEST(UdpInstantiationParsing, ThreeInstances) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y1, y2, y3, a, b, c;\n"
      "  inv u1(y1, a), u2(y2, b), u3(y3, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInsts(r.cu->modules[0]->items);
  ASSERT_EQ(insts.size(), 3u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_EQ(insts[1]->gate_inst_name, "u2");
  EXPECT_EQ(insts[2]->gate_inst_name, "u3");
}

TEST(UdpInstantiationParsing, AllStrengthKeywords) {
  for (const char* s0 : {"supply0", "strong0", "pull0", "weak0"}) {
    for (const char* s1 : {"supply1", "strong1", "pull1", "weak1"}) {
      std::string src =
          "primitive inv(output out, input in);\n"
          "  table 0 : 1; 1 : 0; endtable\n"
          "endprimitive\n"
          "module m;\n"
          "  wire y, a;\n"
          "  inv (" +
          std::string(s0) + ", " + std::string(s1) +
          ") u1(y, a);\n"
          "endmodule\n";
      auto r = Parse(src);
      ASSERT_NE(r.cu, nullptr) << s0 << ", " << s1;
      EXPECT_FALSE(r.has_errors) << s0 << ", " << s1;
      auto insts = FindUdpInsts(r.cu->modules[0]->items);
      ASSERT_EQ(insts.size(), 1u) << s0 << ", " << s1;
      EXPECT_NE(insts[0]->drive_strength0, 0) << s0 << ", " << s1;
      EXPECT_NE(insts[0]->drive_strength1, 0) << s0 << ", " << s1;
    }
  }
}

}  // namespace
