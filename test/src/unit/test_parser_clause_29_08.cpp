#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserA504, UdpInst_BasicNamed) {
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

TEST(ParserA504, UdpInst_Unnamed) {
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

TEST(ParserA504, UdpInst_DriveStrength) {
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

TEST(ParserA504, UdpInst_DriveStrengthReversed) {
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

TEST(ParserA504, UdpInst_DelaySingle) {
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

TEST(ParserA504, UdpInst_DelayRiseFall) {
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

TEST(ParserA504, UdpInst_StrengthAndDelay) {
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

TEST(ParserA504, UdpInst_MultipleInstances) {
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

TEST(ParserA504, UdpInst_MultipleWithStrengthDelay) {
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

TEST(ParserA504, UdpInst_InstanceArray) {
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

TEST(ParserA504, UdpInst_SingleInput) {
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

TEST(ParserA504, UdpInst_ManyInputs) {
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

TEST(ParserA504, UdpInst_WithAttributes) {
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

TEST(ParserSection29, UdpInstance) {
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

}
