// Tests for §28.5 — Switch-level modeling (tran, mos, cmos)

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

TEST(ParserSection28, PassGateTran) {
  auto r = Parse(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kTran);
  ASSERT_EQ(item->gate_terminals.size(), 2);
}

TEST(ParserSection28, MosSwitchNmos) {
  auto r = Parse(
      "module m;\n"
      "  nmos n1(out, data, control);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_inst_name, "n1");
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, CmosSwitchCmos) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data, ncontrol, pcontrol);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kCmos);
  EXPECT_EQ(item->gate_inst_name, "c1");
  ASSERT_EQ(item->gate_terminals.size(), 4);
}

TEST(ParserSection28, ElaboratePulldownGate) {
  ElabFixture f;
  auto *design = ElaborateSrc(
      "module top;\n"
      "  wire out;\n"
      "  pulldown (out);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(mod->assigns[0].rhs->int_val, 0);
}
