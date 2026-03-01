// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

static bool HasGateOfKind(const std::vector<ModuleItem*>& items,
                          GateKind kind) {
  for (const auto* item : items)
    if (item->kind == ModuleItemKind::kGateInst && item->gate_kind == kind)
      return true;
  return false;
}

static void VerifyGateInstances(const std::vector<ModuleItem*>& items,
                                GateKind kind,
                                const std::string expected_names[],
                                size_t count) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(items[i]->gate_kind, kind);
    EXPECT_EQ(items[i]->gate_inst_name, expected_names[i]);
    EXPECT_EQ(items[i]->gate_terminals.size(), 3);
  }
}

static void VerifyStrengthDelayInstances(const std::vector<ModuleItem*>& items,
                                         size_t count, int str0, int str1) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(items[i]->drive_strength0, str0);
    EXPECT_EQ(items[i]->drive_strength1, str1);
    EXPECT_NE(items[i]->gate_delay, nullptr);
  }
}

static RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

// 15. Labeled generate blocks (if-generate)
TEST(ParserClause03, Cl3_13_LabeledIfGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  parameter USE_FAST = 1;\n"
      "  if (USE_FAST) begin : fast_path\n"
      "    logic [7:0] result;\n"
      "  end else begin : slow_path\n"
      "    logic [15:0] result;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_gen_if = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found_gen_if = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen_if);
}

// =============================================================================
// LRM §3.7 — Primitives
// =============================================================================
// §3.7:
//       — logic gates and switches instantiated inside a module.
TEST(ParserClause03, Cl3_7_BuiltInPrimitives) {
  auto r = ParseWithPreprocessor(
      "module gate_test(input a, b, c, output w, x, y, z);\n"
      "  and g1(w, a, b);\n"
      "  nand g2(x, a, b, c);\n"
      "  bufif0 g3(y, a, b);\n"
      "  nmos g4(z, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst), 4);
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kAnd));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kNand));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kBufif0));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kNmos));
}

TEST(ParserSection28, BasicAndGate) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->gate_inst_name, "g1");
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, BasicOrGate) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  or (out, a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kOr);
  EXPECT_TRUE(item->gate_inst_name.empty());
  ASSERT_EQ(item->gate_terminals.size(), 4);
}

TEST(ParserSection28, AllNInputGates) {
  auto r = ParseWithPreprocessor(
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
  GateKind expected[] = {GateKind::kAnd, GateKind::kNand, GateKind::kOr,
                         GateKind::kNor, GateKind::kXor,  GateKind::kXnor};
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->items[i]->gate_kind, expected[i]);
  }
}

// --- Drive strength in gate instantiation context ---
TEST(ParserA222, DriveStrengthGateInst) {
  // drive_strength used with gate instantiation
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and (supply0, supply1) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // wire y, a, b creates 3 items; gate is at index 3
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->drive_strength0, 5u);  // supply0 = 5
  EXPECT_EQ(item->drive_strength1, 5u);  // supply1 = 5
}

TEST(ParserSection28, BasicBufGate) {
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  not n1(out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNot);
}

TEST(ParserSection28, GateArrayRange) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nand n[0:3](out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kNand);
}

TEST(ParserSection28, GateArrayWithDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and #5 g[0:7](out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, MultipleInstances) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and g1(a, b, c), g2(d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  std::string expected_names[] = {"g1", "g2"};
  VerifyGateInstances(mod->items, GateKind::kAnd, expected_names, 2);
}

TEST(ParserSection28, MultipleInstancesThree) {
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and (strong0, strong1) #5 g1(a, b, c), g2(d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  VerifyStrengthDelayInstances(mod->items, 2, 4, 4);
}

TEST(ParserSection28, StrengthWithDelay) {
  auto r = ParseWithPreprocessor(
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

TEST(Parser, GateNoInstanceName) {
  auto r = ParseWithPreprocessor("module t; and (out, a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_TRUE(item->gate_inst_name.empty());
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

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
