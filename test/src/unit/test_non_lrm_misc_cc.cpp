// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

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

static Stmt* NthInitialStmt(ParseResult10b& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

namespace {

// --- 21. Assign with system function RHS ---
TEST(ParserSection10, Sec10_6_1_AssignSystemFuncRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [31:0] q;\n"
      "  initial begin\n"
      "    assign q = $random;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

// --- 22. Multiple sequential assigns to same variable ---
TEST(ParserSection10, Sec10_6_1_MultipleAssignsSameVar) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 0;\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kAssign);
  EXPECT_EQ(s0->lhs->text, "q");
  EXPECT_EQ(s1->lhs->text, "q");
}

// --- 23. Deassign multiple variables in sequence ---
TEST(ParserSection10, Sec10_6_1_DeassignMultipleVars) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    deassign a;\n"
      "    deassign b;\n"
      "    deassign c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  auto* s2 = NthInitialStmt(r, 2);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kDeassign);
  EXPECT_EQ(s1->kind, StmtKind::kDeassign);
  EXPECT_EQ(s2->kind, StmtKind::kDeassign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "b");
  EXPECT_EQ(s2->lhs->text, "c");
}

// --- 24. Assign with delay before it ---
TEST(ParserSection10, Sec10_6_1_DelayBeforeAssign) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    #10 assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- 25. Assign inside nested if-else ---
TEST(ParserSection10, Sec10_6_1_AssignNestedIfElse) {
  auto r = Parse(
      "module m;\n"
      "  reg q, a, b;\n"
      "  initial begin\n"
      "    if (a)\n"
      "      if (b)\n"
      "        assign q = 1;\n"
      "      else\n"
      "        assign q = 0;\n"
      "    else\n"
      "      deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // Outer then-branch is another if.
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  // Inner then/else are both assigns.
  EXPECT_EQ(stmt->then_branch->then_branch->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->then_branch->else_branch->kind, StmtKind::kAssign);
  // Outer else-branch is deassign.
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kDeassign);
}

// --- 26. Assign with reduction operator RHS ---
TEST(ParserSection10, Sec10_6_1_AssignReductionRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  reg parity;\n"
      "  initial begin\n"
      "    assign parity = ^data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kUnary);
}

// --- 27. Assign to vector variable ---
TEST(ParserSection10, Sec10_6_1_AssignToVector) {
  auto r = Parse(
      "module m;\n"
      "  reg [15:0] vec;\n"
      "  initial begin\n"
      "    assign vec = 16'hDEAD;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "vec");
  ASSERT_NE(stmt->rhs, nullptr);
}

}  // namespace
