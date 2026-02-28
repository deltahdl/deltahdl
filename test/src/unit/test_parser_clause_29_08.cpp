// §29.8: UDP instances

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

static std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

namespace {

// =============================================================================
// A.5.4 Production #1: udp_instantiation
// udp_instantiation ::=
//   udp_identifier [ drive_strength ] [ delay2 ]
//   udp_instance { , udp_instance } ;
//
// A.5.4 Production #2: udp_instance
// udp_instance ::=
//   [ name_of_instance ] ( output_terminal , input_terminal
//                          { , input_terminal } )
// =============================================================================
// --- Basic named UDP instance ---
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

// --- Unnamed UDP instance ---
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

// --- Drive strength ---
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

// --- Delay2 ---
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

}  // namespace
