// §9.2.2.2.1: Implicit always_comb sensitivities

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Helper for blocks 11: verify always block has var decl body.
static void VerifyAlwaysVarDecl(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->body->stmts[0]->var_name, "temp");
}

struct ParseResult9i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9i Parse(const std::string& src) {
  ParseResult9i result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// ---------------------------------------------------------------------------
// 19. always_comb with variable declarations in begin-end block.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "    y = temp;\n"
      "  end\n"
      "endmodule\n");
  VerifyAlwaysVarDecl(r);
}

struct ParseResult9h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9h Parse(const std::string& src) {
  ParseResult9h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 11. always_comb with function call
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_FunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b, result;\n"
      "  function logic [7:0] add(input logic [7:0] x, y);\n"
      "    return x + y;\n"
      "  endfunction\n"
      "  always_comb result = add(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kCall);
}

// ---------------------------------------------------------------------------
// 21. always_comb with function call in body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function logic [3:0] mux2(input logic sel,\n"
              "                            input logic [3:0] a, b);\n"
              "    return sel ? a : b;\n"
              "  endfunction\n"
              "  logic sel;\n"
              "  logic [3:0] a, b, y;\n"
              "  always_comb y = mux2(sel, a, b);\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 22. always_comb has implicit sensitivity (no sensitivity list on item)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_ImplicitSensitivity) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  always_comb c = a ^ b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  // always_comb must not have an explicit sensitivity list
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
}

struct ParseResult9c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9c Parse(const std::string& src) {
  ParseResult9c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §9.2.2 -- always_comb procedure
// =============================================================================
TEST(ParserSection9b, AlwaysCombWithAssertion) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    a = b & c;\n"
      "    assert (a != 0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Return the first always-kind module item (any always variant).
static ModuleItem* FirstAlwaysItem(ParseResult9h& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// 3. always_comb has empty sensitivity list.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombEmptySensitivity) {
  auto r = Parse(
      "module m;\n"
      "  always_comb y = a | b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
}

TEST(ParserSection9c, AlwaysCombWithFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function logic [3:0] mux(input logic sel,\n"
              "                           input logic [3:0] a, b);\n"
              "    return sel ? a : b;\n"
              "  endfunction\n"
              "  logic sel;\n"
              "  logic [3:0] a, b, y;\n"
              "  always_comb y = mux(sel, a, b);\n"
              "endmodule\n"));
}

}  // namespace
