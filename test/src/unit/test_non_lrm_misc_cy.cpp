// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

static RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

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

// --- Gate primitive tests ---
TEST(Parser, GateAndInst) {
  auto r = ParseWithPreprocessor("module t; and g1(out, a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->gate_inst_name, "g1");
  EXPECT_EQ(item->gate_terminals.size(), 3u);
}

TEST(Parser, GateNandWithDelay) {
  auto r =
      ParseWithPreprocessor("module t; nand #(5) g2(out, a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNand);
  EXPECT_EQ(item->gate_inst_name, "g2");
  EXPECT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_terminals.size(), 3u);
}

TEST(ParserSection28, PassGateTran) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kTran);
  ASSERT_EQ(item->gate_terminals.size(), 2);
}

TEST(ParserSection28, MosSwitchNmos) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nmos n1(out, data, control);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_inst_name, "n1");
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, CmosSwitchCmos) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  cmos c1(out, data, ncontrol, pcontrol);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kCmos);
  EXPECT_EQ(item->gate_inst_name, "c1");
  ASSERT_EQ(item->gate_terminals.size(), 4);
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

TEST(Parser, GateBufMultiOutput) {
  auto r = ParseWithPreprocessor("module t; buf (o1, o2, in); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kBuf);
  EXPECT_TRUE(item->gate_inst_name.empty());
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, EnableGates) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "  bufif1 (out, in, en);\n"
      "  notif0 (out, in, en);\n"
      "  notif1 (out, in, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 4);
  GateKind expected[] = {GateKind::kBufif0, GateKind::kBufif1,
                         GateKind::kNotif0, GateKind::kNotif1};
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->items[i]->gate_kind, expected[i]);
  }
}

TEST(Parser, GateBufif0) {
  auto r = ParseWithPreprocessor("module t; bufif0 b1(out, in, en); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, PullGates) {
  auto r = ParseWithPreprocessor(
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

TEST(Parser, GateNmos) {
  auto r = ParseWithPreprocessor("module t; nmos (out, in, ctrl); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, GateWithDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and #5 g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(Parser, GateTran) {
  auto r = ParseWithPreprocessor("module t; tran (a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kTran);
  EXPECT_EQ(item->gate_terminals.size(), 2);
}

TEST(ParserSection28, StrengthSpec) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and (strong0, weak1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->drive_strength0, 4);  // strong0 = 4
  EXPECT_EQ(item->drive_strength1, 2);  // weak1 = 2
  EXPECT_EQ(item->gate_inst_name, "g1");
}

TEST(Parser, GateCmos) {
  auto r = ParseWithPreprocessor(
      "module t; cmos (out, in, nctrl, pctrl); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kCmos);
  EXPECT_EQ(item->gate_terminals.size(), 4);
}

TEST(ParserSection28, GateWithParenDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  or #(10) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, StrengthSpecSupply) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nand (supply0, supply1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 5);  // supply0 = 5
  EXPECT_EQ(item->drive_strength1, 5);  // supply1 = 5
}

TEST(ParserSection28, StrengthSpecHighz) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  or (highz0, pull1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1);  // highz0 = 1
  EXPECT_EQ(item->drive_strength1, 3);  // pull1 = 3
}

TEST(Parser, GatePullup) {
  auto r = ParseWithPreprocessor("module t; pullup (o); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kPullup);
  EXPECT_EQ(item->gate_terminals.size(), 1);
}

TEST(ParserSection28, GateWithTwoDelays) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and #(10, 12) a2(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, GateWithThreeDelays) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  bufif0 #(10, 12, 11) b3(out, in, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, GateMinTypMaxDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  bufif0 #(5:7:9, 8:10:12, 15:18:21) b1(io1, io2, dir);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_NE(item->gate_delay, nullptr);
}

// delay3: three values on gate (rise, fall, turn-off).
TEST(ParserA223, Delay3GateThreeValues) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire y, a, b;\n"
      "  bufif1 #(10, 20, 30) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 10u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 20u);
  ASSERT_NE(item->gate_delay_decay, nullptr);
  EXPECT_EQ(item->gate_delay_decay->int_val, 30u);
}

}  // namespace
