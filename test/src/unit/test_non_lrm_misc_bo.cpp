// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult7 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult7 Parse(const std::string& src) {
  ParseResult7 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult7& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt* FirstInitialStmt(ParseResult7& r) {
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

namespace {

// =========================================================================
// §7.3.2: Tagged unions (void members)
// =========================================================================
TEST(ParserSection7, TaggedUnionVoidMember) {
  auto r = Parse(
      "module t;\n"
      "  typedef union tagged {\n"
      "    void Invalid;\n"
      "    int Valid;\n"
      "  } VInt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_EQ(item->typedef_type.struct_members[0].type_kind,
            DataTypeKind::kVoid);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "Invalid");
}

// =========================================================================
// §7.4.1: Packed arrays (multidimensional packed dims)
// =========================================================================
TEST(ParserSection7, MultidimensionalPackedArray) {
  auto r = Parse(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "joe");
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// =========================================================================
// §7.4.3: Memories
// =========================================================================
TEST(ParserSection7, MemoryDeclaration_Type) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mema [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "mema");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(ParserSection7, MemoryDeclaration_Dim) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mema [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto* dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->kind, ExprKind::kBinary);
  EXPECT_EQ(dim->op, TokenKind::kColon);
}

// =========================================================================
// §7.4.6: Operations on arrays
// =========================================================================
TEST(ParserSection7, ArrayAssignWhole) {
  auto r = Parse(
      "module t;\n"
      "  int a[4], b[4];\n"
      "  initial a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// =========================================================================
// §7.5.1: Dynamic array new[]
// =========================================================================
TEST(ParserSection7, DynamicArrayNew) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  initial dyn = new[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection7, DynamicArrayNewWithInit) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  int src[];\n"
      "  initial dyn = new[20](src);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// =========================================================================
// §7.5.2/7.5.3: Dynamic array size() and delete()
// =========================================================================
TEST(ParserSection7, DynamicArraySizeMethod) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  initial x = dyn.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, DynamicArrayDeleteMethod) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  initial dyn.delete();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

// =========================================================================
// §7.6: Array assignments
// =========================================================================
TEST(ParserSection7, ArraySliceAssign) {
  auto r = Parse(
      "module t;\n"
      "  int a[8], b[8];\n"
      "  initial a[3:0] = b[7:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

// =========================================================================
// §7.9: Associative array methods
// =========================================================================
TEST(ParserSection7, AssocArrayNumMethod) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial x = aa.num();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, AssocArrayExistsMethod) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial x = aa.exists(\"key\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, AssocArrayDeleteMethod) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete(\"key\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

// =========================================================================
// §7.10.1: Queue operators
// =========================================================================
TEST(ParserSection7, QueueConcatAssign) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

// =========================================================================
// §7.10.2: Queue methods
// =========================================================================
TEST(ParserSection7, QueuePushBack) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.push_back(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(ParserSection7, QueuePopFront) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial x = q.pop_front();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

}  // namespace
