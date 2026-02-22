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
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FindGateByKind(const std::vector<ModuleItem *> &items,
                                  GateKind kind) {
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kGateInst && item->gate_kind == kind)
      return item;
  }
  return nullptr;
}

static std::vector<ModuleItem *>
FindAllGates(const std::vector<ModuleItem *> &items) {
  std::vector<ModuleItem *> gates;
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kGateInst)
      gates.push_back(item);
  }
  return gates;
}

// =============================================================================
// A.3.1 Production #2: cmos_switch_instance
// cmos_switch_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal , ncontrol_terminal , pcontrol_terminal
//   )
// =============================================================================

TEST(ParserA301, CmosSwitchInst_Unnamed) {
  auto r = Parse("module m;\n"
                 "  cmos (out, in, nctrl, pctrl);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, CmosSwitchInst_Named) {
  auto r = Parse("module m;\n"
                 "  cmos c1(out, in, nctrl, pctrl);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "c1");
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, CmosSwitchInst_RcmosNamed) {
  auto r = Parse("module m;\n"
                 "  rcmos rc1(out, in, nctrl, pctrl);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rc1");
}

// =============================================================================
// A.3.1 Production #3: enable_gate_instance
// enable_gate_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal , enable_terminal )
// =============================================================================

TEST(ParserA301, EnableGateInst_Unnamed) {
  auto r = Parse("module m;\n"
                 "  bufif0 (out, in, en);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, EnableGateInst_Named) {
  auto r = Parse("module m;\n"
                 "  notif1 n1(out, in, en);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "n1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.1 Production #4: mos_switch_instance
// mos_switch_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal , enable_terminal )
// =============================================================================

TEST(ParserA301, MosSwitchInst_Unnamed) {
  auto r = Parse("module m;\n"
                 "  nmos (out, in, gate);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(ParserA301, MosSwitchInst_Named) {
  auto r = Parse("module m;\n"
                 "  pmos p1(out, in, gate);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "p1");
}

// =============================================================================
// A.3.1 Production #5: n_input_gate_instance
// n_input_gate_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal {, input_terminal} )
// =============================================================================

TEST(ParserA301, NInputGateInst_TwoInputs) {
  auto r = Parse("module m;\n"
                 "  and a1(out, in1, in2);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "a1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, NInputGateInst_FourInputs) {
  auto r = Parse("module m;\n"
                 "  nand n1(out, a, b, c, d);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 5u);
}

TEST(ParserA301, NInputGateInst_EightInputs) {
  auto r = Parse("module m;\n"
                 "  xor x1(out, a, b, c, d, e, f, g, h);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 9u);
}

TEST(ParserA301, NInputGateInst_Unnamed) {
  auto r = Parse("module m;\n"
                 "  or (out, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

// =============================================================================
// A.3.1 Production #6: n_output_gate_instance
// n_output_gate_instance ::= [name_of_instance]
//   ( output_terminal {, output_terminal} , input_terminal )
// =============================================================================

TEST(ParserA301, NOutputGateInst_SingleOutput) {
  auto r = Parse("module m;\n"
                 "  buf b1(out, in);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, NOutputGateInst_ThreeOutputs) {
  auto r = Parse("module m;\n"
                 "  not n1(o1, o2, o3, in);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, NOutputGateInst_Unnamed) {
  auto r = Parse("module m;\n"
                 "  buf (o1, o2, in);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.1 Production #7: pass_switch_instance
// pass_switch_instance ::= [name_of_instance] ( inout_terminal , inout_terminal
// )
// =============================================================================

TEST(ParserA301, PassSwitchInst_TranNamed) {
  auto r = Parse("module m;\n"
                 "  tran t1(io1, io2);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, PassSwitchInst_RtranNamed) {
  auto r = Parse("module m;\n"
                 "  rtran rt1(io1, io2);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(ParserA301, PassSwitchInst_Unnamed) {
  auto r = Parse("module m;\n"
                 "  tran (io1, io2);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

// =============================================================================
// A.3.1 Production #8: pass_enable_switch_instance
// pass_enable_switch_instance ::= [name_of_instance]
//   ( inout_terminal , inout_terminal , enable_terminal )
// =============================================================================

TEST(ParserA301, PassEnSwitchInst_Tranif0Named) {
  auto r = Parse("module m;\n"
                 "  tranif0 t1(io1, io2, ctrl);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, PassEnSwitchInst_Tranif1Named) {
  auto r = Parse("module m;\n"
                 "  tranif1 t1(io1, io2, ctrl);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
}

TEST(ParserA301, PassEnSwitchInst_Rtranif0Named) {
  auto r = Parse("module m;\n"
                 "  rtranif0 rt1(io1, io2, ctrl);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(ParserA301, PassEnSwitchInst_Rtranif1Named) {
  auto r = Parse("module m;\n"
                 "  rtranif1 rt1(io1, io2, ctrl);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(ParserA301, PassEnSwitchInst_Unnamed) {
  auto r = Parse("module m;\n"
                 "  tranif0 (io1, io2, ctrl);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

// =============================================================================
// A.3.1 Production #9: pull_gate_instance
// pull_gate_instance ::= [name_of_instance] ( output_terminal )
// =============================================================================

TEST(ParserA301, PullGateInst_PullupNamed) {
  auto r = Parse("module m;\n"
                 "  pullup pu1(net1);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pu1");
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(ParserA301, PullGateInst_PulldownNamed) {
  auto r = Parse("module m;\n"
                 "  pulldown pd1(net1);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pd1");
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(ParserA301, PullGateInst_PullupUnnamed) {
  auto r = Parse("module m;\n"
                 "  pullup (net1);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

// =============================================================================
// Additional gate_instantiation combinations
// =============================================================================

TEST(ParserA301, GateInst_AllNInputGateTypes) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  and  a1(o, i1, i2);\n"
                      "  nand n1(o, i1, i2);\n"
                      "  or   o1(o, i1, i2);\n"
                      "  nor  r1(o, i1, i2);\n"
                      "  xor  x1(o, i1, i2);\n"
                      "  xnor z1(o, i1, i2);\n"
                      "endmodule\n"));
}

TEST(ParserA301, GateInst_AllEnableGateTypes) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  bufif0 b0(o, i, c);\n"
                      "  bufif1 b1(o, i, c);\n"
                      "  notif0 n0(o, i, c);\n"
                      "  notif1 n1(o, i, c);\n"
                      "endmodule\n"));
}

TEST(ParserA301, GateInst_AllMosSwitchTypes) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  nmos  n1(o, i, g);\n"
                      "  pmos  p1(o, i, g);\n"
                      "  rnmos rn1(o, i, g);\n"
                      "  rpmos rp1(o, i, g);\n"
                      "endmodule\n"));
}

TEST(ParserA301, GateInst_AllCmosSwitchTypes) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  cmos  c1(o, i, n, p);\n"
                      "  rcmos rc1(o, i, n, p);\n"
                      "endmodule\n"));
}

TEST(ParserA301, GateInst_AllPassSwitchTypes) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  tran  t1(a, b);\n"
                      "  rtran rt1(a, b);\n"
                      "endmodule\n"));
}

TEST(ParserA301, GateInst_AllPassEnSwitchTypes) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  tranif0  t0(a, b, c);\n"
                      "  tranif1  t1(a, b, c);\n"
                      "  rtranif0 rt0(a, b, c);\n"
                      "  rtranif1 rt1(a, b, c);\n"
                      "endmodule\n"));
}

TEST(ParserA301, GateInst_StrengthOrder_Strength1First) {
  auto r = Parse("module m;\n"
                 "  and (pull1, strong0) a1(out, in1, in2);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(ParserA301, GateInst_DelayWithMinTypMax) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  and #(1:2:3, 4:5:6) a1(out, in1, in2);\n"
                      "endmodule\n"));
}

TEST(ParserA301, GateInst_ComplexTerminalExpressions) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  and a1(out[0], in1[3:0], in2[7:4]);\n"
                      "endmodule\n"));
}

TEST(ParserA301, GateInst_NamedUnnamedMixedInMulti) {
  auto r = Parse("module m;\n"
                 "  and a1(o1, i1, i2), a2(o2, i3, i4), a3(o3, i5, i6);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 3u);
  EXPECT_EQ(gates[0]->gate_inst_name, "a1");
  EXPECT_EQ(gates[1]->gate_inst_name, "a2");
  EXPECT_EQ(gates[2]->gate_inst_name, "a3");
}

TEST(ParserA301, GateInst_SharedStrengthAcrossInstances) {
  auto r = Parse("module m;\n"
                 "  and (weak0, weak1) a1(o1, i1, i2), a2(o2, i3, i4);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, gates[1]->drive_strength0);
  EXPECT_EQ(gates[0]->drive_strength1, gates[1]->drive_strength1);
}

TEST(ParserA301, GateInst_SharedDelayAcrossInstances) {
  auto r = Parse("module m;\n"
                 "  or #5 o1(out1, a, b), o2(out2, c, d);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_NE(gates[0]->gate_delay, nullptr);
  EXPECT_NE(gates[1]->gate_delay, nullptr);
}

} // namespace
