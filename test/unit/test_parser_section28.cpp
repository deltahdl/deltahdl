#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Parse helper ---

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// --- Elaboration helper ---

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// =============================================================
// Section 28: Gate-Level Modeling
// =============================================================

// --- Basic gate parsing (already works) ---

TEST(ParserSection28, BasicAndGate) {
  auto r = Parse(
      "module m;\n"
      "  and g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->gate_inst_name, "g1");
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, BasicOrGate) {
  auto r = Parse(
      "module m;\n"
      "  or (out, a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kOr);
  EXPECT_TRUE(item->gate_inst_name.empty());
  ASSERT_EQ(item->gate_terminals.size(), 4);
}

TEST(ParserSection28, BasicBufGate) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBuf);
  EXPECT_EQ(item->gate_inst_name, "b1");
  ASSERT_EQ(item->gate_terminals.size(), 2);
}

TEST(ParserSection28, BasicNotGate) {
  auto r = Parse(
      "module m;\n"
      "  not n1(out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNot);
}

TEST(ParserSection28, GateWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  and #5 g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, GateWithParenDelay) {
  auto r = Parse(
      "module m;\n"
      "  or #(10) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->gate_delay, nullptr);
}

// --- Strength specifications (LRM section 28.7) ---

TEST(ParserSection28, StrengthSpec) {
  auto r = Parse(
      "module m;\n"
      "  and (strong0, weak1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->drive_strength0, 4);  // strong0 = 4
  EXPECT_EQ(item->drive_strength1, 2);  // weak1 = 2
  EXPECT_EQ(item->gate_inst_name, "g1");
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, StrengthSpecSupply) {
  auto r = Parse(
      "module m;\n"
      "  nand (supply0, supply1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 5);  // supply0 = 5
  EXPECT_EQ(item->drive_strength1, 5);  // supply1 = 5
}

TEST(ParserSection28, StrengthSpecHighz) {
  auto r = Parse(
      "module m;\n"
      "  or (highz0, pull1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1);  // highz0 = 1
  EXPECT_EQ(item->drive_strength1, 3);  // pull1 = 3
}

TEST(ParserSection28, StrengthWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  and (strong0, strong1) #5 g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 4);  // strong0
  EXPECT_EQ(item->drive_strength1, 4);  // strong1
  EXPECT_NE(item->gate_delay, nullptr);
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

// --- Multiple instances per statement (LRM section 28.3) ---

TEST(ParserSection28, MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  and g1(a, b, c), g2(d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);

  auto* g1 = mod->items[0];
  EXPECT_EQ(g1->gate_kind, GateKind::kAnd);
  EXPECT_EQ(g1->gate_inst_name, "g1");
  ASSERT_EQ(g1->gate_terminals.size(), 3);

  auto* g2 = mod->items[1];
  EXPECT_EQ(g2->gate_kind, GateKind::kAnd);
  EXPECT_EQ(g2->gate_inst_name, "g2");
  ASSERT_EQ(g2->gate_terminals.size(), 3);
}

TEST(ParserSection28, MultipleInstancesThree) {
  auto r = Parse(
      "module m;\n"
      "  nand n1(a, b, c), n2(d, e, f), n3(g, h, i);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 3);
  EXPECT_EQ(mod->items[0]->gate_inst_name, "n1");
  EXPECT_EQ(mod->items[1]->gate_inst_name, "n2");
  EXPECT_EQ(mod->items[2]->gate_inst_name, "n3");
}

TEST(ParserSection28, MultipleInstancesNoNames) {
  auto r = Parse(
      "module m;\n"
      "  or (a, b, c), (d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_TRUE(mod->items[0]->gate_inst_name.empty());
  EXPECT_TRUE(mod->items[1]->gate_inst_name.empty());
}

TEST(ParserSection28, MultipleInstancesWithStrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  and (strong0, strong1) #5 g1(a, b, c), g2(d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->drive_strength0, 4);
  EXPECT_EQ(mod->items[0]->drive_strength1, 4);
  EXPECT_NE(mod->items[0]->gate_delay, nullptr);
  EXPECT_EQ(mod->items[1]->drive_strength0, 4);
  EXPECT_EQ(mod->items[1]->drive_strength1, 4);
  EXPECT_NE(mod->items[1]->gate_delay, nullptr);
}

// --- All gate kinds ---

TEST(ParserSection28, AllNInputGates) {
  auto r = Parse(
      "module m;\n"
      "  and (o, a, b);\n"
      "  nand (o, a, b);\n"
      "  or (o, a, b);\n"
      "  nor (o, a, b);\n"
      "  xor (o, a, b);\n"
      "  xnor (o, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 6);
  EXPECT_EQ(mod->items[0]->gate_kind, GateKind::kAnd);
  EXPECT_EQ(mod->items[1]->gate_kind, GateKind::kNand);
  EXPECT_EQ(mod->items[2]->gate_kind, GateKind::kOr);
  EXPECT_EQ(mod->items[3]->gate_kind, GateKind::kNor);
  EXPECT_EQ(mod->items[4]->gate_kind, GateKind::kXor);
  EXPECT_EQ(mod->items[5]->gate_kind, GateKind::kXnor);
}

TEST(ParserSection28, EnableGates) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "  bufif1 (out, in, en);\n"
      "  notif0 (out, in, en);\n"
      "  notif1 (out, in, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 4);
  EXPECT_EQ(mod->items[0]->gate_kind, GateKind::kBufif0);
  EXPECT_EQ(mod->items[1]->gate_kind, GateKind::kBufif1);
  EXPECT_EQ(mod->items[2]->gate_kind, GateKind::kNotif0);
  EXPECT_EQ(mod->items[3]->gate_kind, GateKind::kNotif1);
}

TEST(ParserSection28, PullGates) {
  auto r = Parse(
      "module m;\n"
      "  pullup (out);\n"
      "  pulldown (out);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->gate_kind, GateKind::kPullup);
  EXPECT_EQ(mod->items[1]->gate_kind, GateKind::kPulldown);
}

// =============================================================
// Section 29: User-Defined Primitives
// =============================================================

TEST(ParserSection29, CombinationalUdp) {
  auto r = Parse(
      "primitive mux(output out, input a, b, sel);\n"
      "  table\n"
      "    0 ? 0 : 0;\n"
      "    1 ? 0 : 1;\n"
      "    ? 0 1 : 0;\n"
      "    ? 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "mux");
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 3);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "sel");
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 4);
  // First row: 0 ? 0 : 0
  EXPECT_EQ(udp->table[0].inputs.size(), 3);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], '?');
  EXPECT_EQ(udp->table[0].inputs[2], '0');
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[0].current_state, 0);
}

TEST(ParserSection29, SequentialUdp) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2);
  ASSERT_EQ(udp->table.size(), 2);
  // First row: 0 r : ? : 0
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
  EXPECT_EQ(udp->table[0].current_state, '?');
  EXPECT_EQ(udp->table[0].output, '0');
}

TEST(ParserSection29, UdpTableSpecialChars) {
  auto r = Parse(
      "primitive edge_detect(output reg q, input d, clk);\n"
      "  table\n"
      "    ? f : ? : 1;\n"
      "    ? p : ? : 0;\n"
      "    * ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 3);
  EXPECT_EQ(udp->table[0].inputs[1], 'f');
  EXPECT_EQ(udp->table[1].inputs[1], 'p');
  EXPECT_EQ(udp->table[2].inputs[0], '*');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(ParserSection29, UdpMultiple) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive buf2(output out, input in);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 2);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
  EXPECT_EQ(r.cu->udps[1]->name, "buf2");
}

TEST(ParserSection29, UdpCoexistsWithModule) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

// =============================================================
// Gate elaboration
// =============================================================

TEST(ParserSection28, ElaborateAndGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  and g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  // Gate should produce a continuous assign.
  ASSERT_GE(mod->assigns.size(), 1);
  auto& ca = mod->assigns[0];
  EXPECT_NE(ca.lhs, nullptr);
  EXPECT_NE(ca.rhs, nullptr);
  // The rhs should be a binary '&' expression.
  EXPECT_EQ(ca.rhs->op, TokenKind::kAmp);
}

TEST(ParserSection28, ElaborateOrGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  or g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].rhs->op, TokenKind::kPipe);
}

TEST(ParserSection28, ElaborateNandGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  nand g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // nand -> ~(a & b): unary kTilde wrapping binary kAmp.
  auto* rhs = mod->assigns[0].rhs;
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  EXPECT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
}

TEST(ParserSection28, ElaborateXorGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  xor g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].rhs->op, TokenKind::kCaret);
}

TEST(ParserSection28, ElaborateBufGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, in;\n"
      "  buf b1(out, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // buf: out = in (identity), rhs is an identifier.
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIdentifier);
}

TEST(ParserSection28, ElaborateNotGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, in;\n"
      "  not n1(out, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // not: out = ~in, rhs is unary kTilde.
  EXPECT_EQ(mod->assigns[0].rhs->op, TokenKind::kTilde);
}

TEST(ParserSection28, ElaborateMultiInputAnd) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b, c;\n"
      "  and g1(out, a, b, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // 3-input and: (a & b) & c -- nested binary.
  auto* rhs = mod->assigns[0].rhs;
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserSection28, ElaboratePullupGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out;\n"
      "  pullup (out);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // pullup: out = 1'b1
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(mod->assigns[0].rhs->int_val, 1);
}

TEST(ParserSection28, ElaboratePulldownGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out;\n"
      "  pulldown (out);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(mod->assigns[0].rhs->int_val, 0);
}
