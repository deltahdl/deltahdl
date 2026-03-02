// §16.12.6: If-else property

#include "fixture_parser.h"

using namespace delta;

namespace {

// property_expr ::= if (...) property_expr [else property_expr]
TEST(ParserA210, PropertyExpr_IfElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    if (mode) a |-> b else c |-> d);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_IfNoElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    if (mode) a |-> b);\n"
              "endmodule\n"));
}

using VerifyParseTest = ProgramTestParse;

// Assert property with if-else inside property expression.
TEST(ParserSection16, Sec16_5_1_PropertyIfElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk)\n"
              "    if (mode) a |-> b\n"
              "    else a |-> c);\n"
              "endmodule\n"));
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// --- F.15: Property if-else ---
TEST(ParserAnnexF, AnnexFPropertyIfElse) {
  auto r = Parse(
      "module m;\n"
      "  property p_cond;\n"
      "    @(posedge clk) if (mode) a |-> b; else c |-> d;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

// --- Test helpers ---
struct ParseResult16b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16b Parse(const std::string& src) {
  ParseResult16b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §16.14.6.2 Property if-else
// =============================================================================
TEST(ParserSection16, PropertyIfElse) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk)\n"
      "    if (mode) a |-> b\n"
      "    else a |-> c);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
