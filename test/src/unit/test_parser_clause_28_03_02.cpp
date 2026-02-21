// Tests for §28.3.2 — N-input gates (and, nand, or, nor, xor, xnor)

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

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

TEST(ParserSection28, BasicAndGate) {
  auto r = Parse(
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
  GateKind expected[] = {GateKind::kAnd, GateKind::kNand, GateKind::kOr,
                         GateKind::kNor, GateKind::kXor,  GateKind::kXnor};
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->items[i]->gate_kind, expected[i]);
  }
}
