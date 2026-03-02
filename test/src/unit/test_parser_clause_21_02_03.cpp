// §21.2.3: Continuous monitoring

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, MonitorOnOff) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $monitoron;\n"
              "    $monitoroff;\n"
              "  end\n"
              "endmodule\n"));
}

struct ParseResult4b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static Stmt* FirstInitialStmt(ParseResult4b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 9. $monitor system call
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_MonitorSystemCall) {
  auto r = Parse(
      "module m;\n"
      "  reg a;\n"
      "  initial begin\n"
      "    $monitor(\"a=%b\", a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$monitor");
}

TEST(ParserSection21, MonitorBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $monitor(\"a=%b b=%b\", a, b);\n"
              "endmodule\n"));
}

}  // namespace
