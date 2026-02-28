// §9.4.1: Delay control

#include "fixture_parser.h"

using namespace delta;

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

namespace {

// Statement delay: #delay_value in procedural context.
TEST(ParserA223, DelayValueInStatement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial #10 $display(\"hello\");\n"
              "endmodule"));
}

struct ParseResult9d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9d Parse(const std::string& src) {
  ParseResult9d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialBody(ParseResult9d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) return item->body;
  }
  return nullptr;
}

static Stmt* FirstInitialStmt(ParseResult9d& r) {
  auto* body = FirstInitialBody(r);
  if (body && body->kind == StmtKind::kBlock) {
    return body->stmts.empty() ? nullptr : body->stmts[0];
  }
  return body;
}

// =============================================================================
// LRM section 9.4 -- Procedural timing controls
// Zero-delay, chained delays, delay expressions.
// =============================================================================
TEST(ParserSection9c, ZeroDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #0 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

}  // namespace
