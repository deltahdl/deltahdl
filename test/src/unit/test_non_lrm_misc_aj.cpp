// Non-LRM tests

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

static ModuleItem* FindAlias(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kAlias) return item;
  }
  return nullptr;
}

// Helpers to extract items from the first module.
static ModuleItem* FindItem(const std::vector<ModuleItem*>& items,
                            ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
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

// =============================================================================
// A.6.1 Production: continuous_assign (parsing)
// continuous_assign ::=
//   assign [ drive_strength ] [ delay3 ] list_of_net_assignments ;
//   | assign [ delay_control ] list_of_variable_assignments ;
// =============================================================================
TEST(ParserA601, ContinuousAssign_Basic) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  ASSERT_NE(cas[0]->assign_lhs, nullptr);
  ASSERT_NE(cas[0]->assign_rhs, nullptr);
}

TEST(ParserA601, ContinuousAssign_DriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 4u);
  EXPECT_EQ(cas[0]->drive_strength1, 2u);
}

TEST(ParserA601, ContinuousAssign_DriveStrengthReversed) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull1, supply0) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 5u);
  EXPECT_EQ(cas[0]->drive_strength1, 3u);
}

TEST(ParserA601, ContinuousAssign_DelaySingle) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #10 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_EQ(cas[0]->assign_delay_fall, nullptr);
  EXPECT_EQ(cas[0]->assign_delay_decay, nullptr);
}

TEST(ParserA601, ContinuousAssign_DelayRiseFall) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_NE(cas[0]->assign_delay_fall, nullptr);
  EXPECT_EQ(cas[0]->assign_delay_decay, nullptr);
}

TEST(ParserA601, ContinuousAssign_DelayRiseFallDecay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10, 15) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_NE(cas[0]->assign_delay_fall, nullptr);
  EXPECT_NE(cas[0]->assign_delay_decay, nullptr);
}

TEST(ParserA601, ContinuousAssign_StrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign (pull0, pull1) #5 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->drive_strength0, 0u);
  EXPECT_NE(cas[0]->drive_strength1, 0u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
}

// =============================================================================
// A.6.1 Production: list_of_net_assignments (parsing)
// list_of_net_assignments ::= net_assignment { , net_assignment }
// =============================================================================
TEST(ParserA601, ListOfNetAssignments_Two) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 2u);
  EXPECT_EQ(cas[0]->assign_lhs->text, "a");
  EXPECT_EQ(cas[1]->assign_lhs->text, "c");
}

TEST(ParserA601, ListOfNetAssignments_Three) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d, e, f;\n"
      "  assign a = b, c = d, e = f;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 3u);
  EXPECT_EQ(cas[0]->assign_lhs->text, "a");
  EXPECT_EQ(cas[1]->assign_lhs->text, "c");
  EXPECT_EQ(cas[2]->assign_lhs->text, "e");
}

TEST(ParserA601, ListOfNetAssignments_SharedStrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign (strong0, strong1) #10 a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 2u);
  EXPECT_EQ(cas[0]->drive_strength0, 4u);
  EXPECT_EQ(cas[1]->drive_strength0, 4u);
  EXPECT_EQ(cas[0]->drive_strength1, 4u);
  EXPECT_EQ(cas[1]->drive_strength1, 4u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_NE(cas[1]->assign_delay, nullptr);
}

// =============================================================================
// A.6.1 Production: net_assignment (parsing)
// net_assignment ::= net_lvalue = expression
// =============================================================================
TEST(ParserA601, NetAssignment_ConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] sum;\n"
      "  wire carry;\n"
      "  assign {carry, sum} = 5'b10101;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->assign_lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserA601, NetAssignment_ExprRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] a, b, sum;\n"
      "  assign sum = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->assign_rhs->kind, ExprKind::kBinary);
}

TEST(ParserA601, NetAssignment_TernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, sel, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_rhs, nullptr);
}

// =============================================================================
// A.6.1 Production: net_alias (parsing)
// net_alias ::= alias net_lvalue = net_lvalue { = net_lvalue } ;
// =============================================================================
TEST(ParserA601, NetAlias_TwoNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 2u);
}

TEST(ParserA601, NetAlias_ThreeNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 3u);
}

TEST(ParserA601, NetAlias_FourNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  alias a = b = c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 4u);
}

TEST(ParserA601, NetAlias_BitSelect) {
  // §10.11: alias with bit-selects for byte-swapping
  auto r = Parse(
      "module m;\n"
      "  wire [31:0] A, B;\n"
      "  alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 2u);
}

// =============================================================================
// A.6.2 Production: initial_construct
// initial_construct ::= initial statement_or_null
// =============================================================================
TEST(ParserA602, InitialConstruct_SingleStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserA602, InitialConstruct_BeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ParserA602, InitialConstruct_NullStmt) {
  // initial with null statement (just a semicolon)
  auto r = Parse(
      "module m;\n"
      "  initial ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kNull);
}

TEST(ParserA602, InitialConstruct_Multiple) {
  // Multiple initial blocks in the same module
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 0;\n"
      "  initial c = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto inits =
      FindItems(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  EXPECT_EQ(inits.size(), 3u);
}

// =============================================================================
// A.6.2 Production: always_construct
// always_construct ::= always_keyword statement
// =============================================================================
TEST(ParserA602, AlwaysConstruct_PlainAlways) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserA602, AlwaysConstruct_AlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
}

}  // namespace
