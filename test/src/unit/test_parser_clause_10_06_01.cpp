// §10.6.1: The assign and deassign procedural statements

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

// =============================================================================
// A.6.2 Production: procedural_continuous_assignment
// procedural_continuous_assignment ::=
//   assign variable_assignment
//   | deassign variable_lvalue
//   | force variable_assignment
//   | force net_assignment
//   | release variable_lvalue
//   | release net_lvalue
// =============================================================================
TEST(ParserA602, ProceduralAssign_Basic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin assign q = d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, ProceduralDeassign_Basic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin deassign q; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  EXPECT_NE(stmt->lhs, nullptr);
}

TEST(ParserA602, ProceduralAssign_WithBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial begin assign q[0] = d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

// --- 28. Assign in task body ---
TEST(ParserSection10, Sec10_6_1_AssignInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg q;\n"
              "  task set_q;\n"
              "    assign q = 1;\n"
              "  endtask\n"
              "  task clear_q;\n"
              "    deassign q;\n"
              "  endtask\n"
              "endmodule\n"));
}

// Helper: extract 4 initial statements and verify non-null.
struct FourStmts {
  Stmt* s0;
  Stmt* s1;
  Stmt* s2;
  Stmt* s3;
};

static FourStmts Get4InitialStmts(auto& r) {
  FourStmts fs;
  fs.s0 = NthInitialStmt(r, 0);
  fs.s1 = NthInitialStmt(r, 1);
  fs.s2 = NthInitialStmt(r, 2);
  fs.s3 = NthInitialStmt(r, 3);
  EXPECT_NE(fs.s0, nullptr);
  EXPECT_NE(fs.s1, nullptr);
  EXPECT_NE(fs.s2, nullptr);
  EXPECT_NE(fs.s3, nullptr);
  return fs;
}

struct ParseResult10d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10d Parse(const std::string& src) {
  ParseResult10d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* NthInitialStmt(ParseResult10d& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

// --- 29. Assign/deassign interleaved with nonblocking assigns ---
TEST(ParserSection10, Sec10_6_1_InterleavedWithNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "    q <= 0;\n"
      "    deassign q;\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto [s0, s1, s2, s3] = Get4InitialStmts(r);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s2->kind, StmtKind::kDeassign);
  EXPECT_EQ(s3->kind, StmtKind::kNonblockingAssign);
}

// --- 30. Full D-FF with assign/deassign and always @(posedge) ---
TEST(ParserSection10, Sec10_6_1_FullDFlipFlopPattern) {
  auto r = Parse(
      "module dff_full(output reg q, input d, clr, pre, clk);\n"
      "  always @(clr or pre) begin\n"
      "    if (!clr)\n"
      "      assign q = 0;\n"
      "    else if (!pre)\n"
      "      assign q = 1;\n"
      "    else\n"
      "      deassign q;\n"
      "  end\n"
      "  always @(posedge clk)\n"
      "    q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "dff_full");
  // Should have at least two always blocks.
  int always_count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) always_count++;
  }
  EXPECT_GE(always_count, 2);
}

}  // namespace
