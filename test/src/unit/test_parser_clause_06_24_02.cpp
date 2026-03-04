// §6.24.2: $cast dynamic casting

#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

// =========================================================================
// §6.24.2: Dynamic casting — $cast
// =========================================================================
TEST(ParserSection6, DynamicCastTask) {
  // §6.24.2: $cast as a task call.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef enum { A, B, C } abc_t;\n"
              "  initial begin\n"
              "    abc_t e;\n"
              "    $cast(e, 1);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, DynamicCastFunction) {
  // §6.24.2: $cast as a function returns int.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef enum { X, Y, Z } xyz_t;\n"
              "  initial begin\n"
              "    xyz_t e;\n"
              "    int ok;\n"
              "    ok = $cast(e, 2);\n"
              "  end\n"
              "endmodule\n"));
}

struct ParseResult6 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6 Parse(const std::string& src) {
  ParseResult6 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult6& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// =========================================================================
// §6.24.1 -- Static casting (additional tests)
// =========================================================================
// =========================================================================
// §6.24.2 -- Dynamic casting ($cast)
// =========================================================================
TEST(ParserSection6, DynamicCastCall) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $cast(d, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$cast");
}

TEST(ParserSection6, DynamicCastInCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if ($cast(d, b))\n"
      "      $display(\"cast ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

TEST(ParserSection6, DynamicCastAssignResult) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    int ok;\n"
      "    ok = $cast(d, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
