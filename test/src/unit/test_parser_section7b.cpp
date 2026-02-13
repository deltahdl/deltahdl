#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult7b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult7b Parse(const std::string& src) {
  ParseResult7b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult7b& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt* FirstInitialStmt(ParseResult7b& r) {
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
// §7.4: Struct variable declaration (non-typedef)
// =========================================================================

TEST(ParserSection7, StructVariableDecl) {
  auto r = Parse(
      "module t;\n"
      "  struct { int a; int b; } my_var;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_EQ(item->name, "my_var");
}

// =========================================================================
// §7.12.1: Array locator method 'unique' (keyword as method name)
// =========================================================================

TEST(ParserSection7, ArrayLocatorUnique) {
  auto r = Parse(
      "module t;\n"
      "  int s[] = '{10, 10, 3, 20, 20, 10};\n"
      "  int qi[$];\n"
      "  initial qi = s.unique;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

// =========================================================================
// §7.12.3: Array reduction methods 'and', 'or', 'xor' (keywords as names)
// =========================================================================

TEST(ParserSection7, ArrayReductionAnd) {
  auto r = Parse(
      "module t;\n"
      "  byte b[] = '{1, 3, 5, 7};\n"
      "  initial y = b.and;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, ArrayReductionOr) {
  auto r = Parse(
      "module t;\n"
      "  byte b[] = '{1, 2, 3, 4};\n"
      "  initial y = b.or;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, ArrayReductionXor) {
  auto r = Parse(
      "module t;\n"
      "  byte b[] = '{1, 2, 3, 4};\n"
      "  initial y = b.xor;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

// =========================================================================
// §7.10.4: Empty concatenation {} to clear queue
// =========================================================================

TEST(ParserSection7, EmptyConcatClearQueue_Parse) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection7, EmptyConcatClearQueue_Rhs) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_TRUE(stmt->rhs->elements.empty());
}

TEST(ParserSection7, UnionWithNestedStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef union tagged {\n"
      "    struct {\n"
      "      bit [4:0] reg1, reg2;\n"
      "    } Add;\n"
      "    bit [9:0] Jmp;\n"
      "  } Instr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}
