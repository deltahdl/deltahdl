#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §A.5.4 udp_instantiation ::=
//   udp_identifier [ drive_strength ] [ delay2 ]
//   udp_instance { , udp_instance } ;

TEST(ParserA54, UdpInstBasic) {
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

// §A.5.4 udp_instance ::= [ name_of_instance ] ( output, input {, input} )

TEST(ParserA54, UdpInstUnnamed) {
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

TEST(ParserA54, UdpInstMultipleInputs) {
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

// Multiple instances in one statement

TEST(ParserA54, UdpInstMultipleInstances) {
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

// §A.5.4 [ drive_strength ]

TEST(ParserA54, UdpInstWithDriveStrength) {
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

// §A.5.4 [ delay2 ] — single delay value

TEST(ParserA54, UdpInstWithDelaySingle) {
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

// §A.5.4 [ delay2 ] — two delay values (rise, fall)

TEST(ParserA54, UdpInstWithDelayTwo) {
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

// Both drive_strength and delay2

TEST(ParserA54, UdpInstStrengthAndDelay) {
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

// name_of_instance with unpacked dimension (instance array)

TEST(ParserA54, UdpInstWithInstanceArray) {
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

// No drive_strength, no delay — defaults

TEST(ParserA54, UdpInstNoStrengthNoDelay) {
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

// Strength shared across multiple instances

TEST(ParserA54, UdpInstStrengthSharedAcrossInstances) {
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

// Sequential UDP instantiation

TEST(ParserA54, UdpInstSequential) {
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

}  // namespace
