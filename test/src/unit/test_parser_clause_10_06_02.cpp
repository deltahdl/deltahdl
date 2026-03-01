// §10.6.2: The force and release procedural statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

namespace {

TEST(ParserA602, Force_Variable) {
  // force variable_assignment
  auto r = Parse(
      "module m;\n"
      "  initial begin force q = 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, Force_Net) {
  // force net_assignment
  auto r = Parse(
      "module m;\n"
      "  initial begin force net_a = 0; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
}

TEST(ParserA602, Release_Variable) {
  auto r = Parse(
      "module m;\n"
      "  initial begin release q; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
  EXPECT_NE(stmt->lhs, nullptr);
}

TEST(ParserA602, Release_Net) {
  auto r = Parse(
      "module m;\n"
      "  initial begin release net_a; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
}

TEST(ParserA602, Force_WithConcat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin force {a, b} = 2'b11; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserA602, Release_WithConcat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin release {a, b}; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
}

struct ParseResult10b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10b Parse(const std::string& src) {
  ParseResult10b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult10b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

TEST(ParserSection10, ForceNet) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin\n"
      "    force bus = 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, ReleaseNet) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin\n"
      "    release bus;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
  ASSERT_NE(stmt->lhs, nullptr);
}

// §10.6.2: force statement
TEST(ParserA604, StmtItemForceStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    force x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
}

// §10.6.2: release statement
TEST(ParserA604, StmtItemReleaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    release x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
}

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

TEST(ParserSection38, VpiSystemCallForce) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    force sig = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
