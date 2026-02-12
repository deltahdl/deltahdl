#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult5 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult5 Parse(const std::string& src) {
  ParseResult5 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult5& r) {
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

static bool ParseOk5(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

struct ParseDiag5 {
  SourceManager mgr;
  Arena arena;
  DiagEngine* diag = nullptr;
  CompilationUnit* cu = nullptr;
};

static ParseDiag5 ParseWithDiag(const std::string& src) {
  ParseDiag5 result;
  auto fid = result.mgr.AddFile("<test>", src);
  result.diag = new DiagEngine(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, *result.diag);
  Parser parser(lexer, result.arena, *result.diag);
  result.cu = parser.Parse();
  return result;
}

// --- §5.10/§5.11: Assignment patterns ---

TEST(ParserSection5, AssignmentPatternPositional) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 3u);
  EXPECT_TRUE(rhs->pattern_keys.empty());
}

TEST(ParserSection5, AssignmentPatternNamed) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{a: 0, b: 1};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 2u);
  ASSERT_EQ(rhs->pattern_keys.size(), 2u);
  EXPECT_EQ(rhs->pattern_keys[0], "a");
  EXPECT_EQ(rhs->pattern_keys[1], "b");
}

TEST(ParserSection5, AssignmentPatternDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->pattern_keys.size(), 1u);
  EXPECT_EQ(rhs->pattern_keys[0], "default");
}

// --- §5.12: Attributes ---

TEST(ParserSection5, AttributeOnModuleItem) {
  auto r = Parse(
      "module t;\n"
      "  (* full_case *)\n"
      "  logic [7:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "full_case");
  EXPECT_EQ(item->attrs[0].value, nullptr);
}

TEST(ParserSection5, AttributeWithValue) {
  auto r = Parse(
      "module t;\n"
      "  (* synthesis, optimize_power = 1 *)\n"
      "  logic y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].name, "synthesis");
  EXPECT_EQ(item->attrs[0].value, nullptr);
  EXPECT_EQ(item->attrs[1].name, "optimize_power");
  ASSERT_NE(item->attrs[1].value, nullptr);
}

// --- §5.13: Built-in method calls ---

TEST(ParserSection5, BuiltInMethodCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  // The callee_expr should be the full member-access expression.
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
}

// --- Unpacked range dimensions [M:N] ---

TEST(ParserSection5, UnpackedDim_Range) {
  EXPECT_TRUE(ParseOk5("module m; int a[1:0]; endmodule"));
}

TEST(ParserSection5, UnpackedDim_MultiRange) {
  EXPECT_TRUE(ParseOk5("module m; int a[1:2][1:3]; endmodule"));
}

TEST(ParserSection5, UnpackedDim_Typedef) {
  EXPECT_TRUE(ParseOk5("module m; typedef int triple[1:3]; endmodule"));
}

// --- Assignment pattern type/default/integer keys ---

TEST(ParserSection5, AssignmentPattern_TypeKey) {
  EXPECT_TRUE(
      ParseOk5("module m;\n"
               "  typedef struct { int x; int y; } ms_t;\n"
               "  ms_t ms = '{int:0, int:1};\n"
               "endmodule"));
}

TEST(ParserSection5, AssignmentPattern_DefaultKey) {
  EXPECT_TRUE(
      ParseOk5("module m;\n"
               "  typedef struct { int x; int y; } ms_t;\n"
               "  ms_t ms = '{default:1};\n"
               "endmodule"));
}

TEST(ParserSection5, AssignmentPattern_IntKey) {
  EXPECT_TRUE(
      ParseOk5("module m;\n"
               "  typedef int triple[1:3];\n"
               "  triple t = '{1:1, default:0};\n"
               "endmodule"));
}

// --- Comma-separated struct members ---

TEST(ParserSection5, StructMembers_CommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  struct { int X, Y, Z; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.struct_members.size(), 3u);
}

TEST(ParserSection5, StructMembers_Single) {
  EXPECT_TRUE(ParseOk5("module m; struct { int X; } s; endmodule"));
}

// --- Null module items ---

TEST(ParserSection5, ModuleBody_NullItem) {
  EXPECT_TRUE(ParseOk5("module m; ; endmodule"));
}

TEST(ParserSection5, ModuleBody_SemicolonAfterEnd) {
  EXPECT_TRUE(ParseOk5("module m; initial begin end; endmodule"));
}

// --- Attributes before top-level declarations ---

TEST(ParserSection5, TopLevel_AttributeBeforeModule) {
  EXPECT_TRUE(ParseOk5("(* optimize_power *) module m; endmodule"));
}

TEST(ParserSection5, TopLevel_TrailingSemicolonAfterEndmodule) {
  EXPECT_TRUE(ParseOk5("module m; endmodule;"));
}

// --- Attributes in expressions ---

TEST(ParserSection5, Expr_AttributeOnOperator) {
  EXPECT_TRUE(
      ParseOk5("module m;\n"
               "  logic a, b, c;\n"
               "  assign a = b + (* mode = \"cla\" *) c;\n"
               "endmodule"));
}

TEST(ParserSection5, Expr_AttributeOnTernary) {
  EXPECT_TRUE(
      ParseOk5("module m;\n"
               "  logic a, b, c, d;\n"
               "  assign a = b ? (* no_glitch *) c : d;\n"
               "endmodule"));
}

// --- Assignment pattern replication ---

TEST(ParserSection5, AssignmentPattern_Replication) {
  EXPECT_TRUE(
      ParseOk5("module m;\n"
               "  int a[1:3] = '{3{1}};\n"
               "endmodule"));
}

TEST(ParserSection5, AssignmentPattern_NestedReplication) {
  EXPECT_TRUE(
      ParseOk5("module m;\n"
               "  int n[1:2][1:6] = '{2{'{3{4, 5}}}};\n"
               "endmodule"));
}

// --- §9.3.1: Block-level variable declarations ---

TEST(ParserSection5, BlockVarDecl_BuiltinType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  auto* blk = item->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->kind, StmtKind::kBlock);
  ASSERT_EQ(blk->stmts.size(), 1u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(blk->stmts[0]->var_decl_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(blk->stmts[0]->var_name, "x");
}

TEST(ParserSection5, BlockVarDecl_UserDefinedType) {
  EXPECT_TRUE(
      ParseOk5("module m;\n"
               "  typedef struct {int a, b[4];} ab_t;\n"
               "  initial begin\n"
               "    ab_t v1[1:0] [2:0];\n"
               "  end\n"
               "endmodule\n"));
}

TEST(ParserSection5, BlockVarDecl_CommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a, b, c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->stmts.size(), 3u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(blk->stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(blk->stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(blk->stmts[0]->var_name, "a");
  EXPECT_EQ(blk->stmts[1]->var_name, "b");
  EXPECT_EQ(blk->stmts[2]->var_name, "c");
}

TEST(ParserSection5, BlockVarDecl_WithInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->stmts.size(), 1u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_NE(blk->stmts[0]->var_init, nullptr);
}

TEST(ParserSection5, BlockVarDecl_FullStructReplication) {
  EXPECT_TRUE(
      ParseOk5("module top();\n"
               "  struct {int X,Y,Z;} XYZ = '{3{1}};\n"
               "  typedef struct {int a,b[4];} ab_t;\n"
               "  int a,b,c;\n"
               "  initial begin\n"
               "    ab_t v1[1:0] [2:0];\n"
               "    v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
               "  end\n"
               "endmodule\n"));
}

// --- §5.7.1: Sized literal overflow warning ---

TEST(ParserSection5, SizedLiteral_NoOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(ParserSection5, SizedLiteral_Overflow_Warning) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hFF;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
}

TEST(ParserSection5, SizedLiteral_ExactFit) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(ParserSection5, SizedLiteral_OneBitOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 3'b1111;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
}
