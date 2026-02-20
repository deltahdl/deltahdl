#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

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

// --- Drive strength AND delay2 ---

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

// --- Multiple instances per statement ---

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
  // Both share same strength and delay
  EXPECT_NE(insts[0]->drive_strength0, 0);
  EXPECT_NE(insts[1]->drive_strength0, 0);
  EXPECT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_NE(insts[1]->gate_delay, nullptr);
}

// --- Instance arrays ---

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

// --- Multiple input terminals ---

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

// --- Attributes ---

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

// --- Extern UDP declaration used for instantiation ---

TEST(ParserA504, UdpInst_ExternUdp) {
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

}  // namespace
