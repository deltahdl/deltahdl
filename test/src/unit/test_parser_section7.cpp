#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult7 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult7 Parse(const std::string &src) {
  ParseResult7 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem *FirstItem(ParseResult7 &r) {
  if (!r.cu || r.cu->modules.empty())
    return nullptr;
  auto &items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt *FirstInitialStmt(ParseResult7 &r) {
  for (auto *item : r.cu->modules[0]->items) {
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
// §7.2: Structures
// =========================================================================

TEST(ParserSection7, StructBasic) {
  auto r = Parse("module t;\n"
                 "  typedef struct {\n"
                 "    int a;\n"
                 "    logic [7:0] b;\n"
                 "  } my_struct;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
  std::string expected_names[] = {"a", "b"};
  ASSERT_EQ(item->typedef_type.struct_members.size(),
            std::size(expected_names));
  for (size_t i = 0; i < std::size(expected_names); ++i) {
    EXPECT_EQ(item->typedef_type.struct_members[i].name, expected_names[i])
        << "member " << i;
  }
}

TEST(ParserSection7, StructPackedSigned) {
  auto r = Parse("module t;\n"
                 "  typedef struct packed signed {\n"
                 "    int a;\n"
                 "    byte b;\n"
                 "  } packed_s;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_TRUE(item->typedef_type.is_signed);
}

TEST(ParserSection7, StructMemberInit) {
  auto r = Parse("module t;\n"
                 "  typedef struct {\n"
                 "    int addr = 100;\n"
                 "    int crc;\n"
                 "  } packet;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_NE(item->typedef_type.struct_members[0].init_expr, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members[1].init_expr, nullptr);
}

TEST(ParserSection7, StructMemberUnpackedDim) {
  auto r = Parse("module t;\n"
                 "  typedef struct {\n"
                 "    byte data[4];\n"
                 "  } packet;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 1u);
  EXPECT_FALSE(item->typedef_type.struct_members[0].unpacked_dims.empty());
}

// =========================================================================
// §7.3: Unions
// =========================================================================

TEST(ParserSection7, UnionBasic) {
  auto r = Parse("module t;\n"
                 "  typedef union {\n"
                 "    int i;\n"
                 "    shortreal f;\n"
                 "  } num;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

TEST(ParserSection7, UnionTagged) {
  auto r = Parse("module t;\n"
                 "  typedef union tagged {\n"
                 "    void Invalid;\n"
                 "    int Valid;\n"
                 "  } VInt;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

TEST(ParserSection7, UnionSoftPacked) {
  auto r = Parse("module t;\n"
                 "  typedef union soft packed {\n"
                 "    bit [7:0] a;\n"
                 "    bit [3:0] b;\n"
                 "  } soft_u;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_soft);
  EXPECT_TRUE(item->typedef_type.is_packed);
}

// =========================================================================
// §7.4: Packed and unpacked arrays
// =========================================================================

TEST(ParserSection7, UnpackedArraySize) {
  auto r = Parse("module t;\n"
                 "  int arr[8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserSection7, UnpackedArrayRange) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] mem[0:255];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserSection7, MultidimensionalArray) {
  auto r = Parse("module t;\n"
                 "  int matrix[4][8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_GE(item->unpacked_dims.size(), 2u);
}

TEST(ParserSection7, IndexedPartSelectPlus) {
  auto r = Parse("module t;\n"
                 "  initial x = data[3 +: 4];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

TEST(ParserSection7, IndexedPartSelectMinus) {
  auto r = Parse("module t;\n"
                 "  initial x = data[7 -: 4];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

// =========================================================================
// §7.5: Dynamic arrays
// =========================================================================

TEST(ParserSection7, DynamicArrayDecl) {
  auto r = Parse("module t;\n"
                 "  int dyn[];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "dyn");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// =========================================================================
// §7.8: Associative arrays
// =========================================================================

TEST(ParserSection7, AssocArrayWildcard) {
  auto r = Parse("module t;\n"
                 "  integer aa[*];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "aa");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserSection7, AssocArrayStringIndex) {
  auto r = Parse("module t;\n"
                 "  int scores[string];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "scores");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
}

TEST(ParserSection7, AssocArrayStringIndex_DimExpr) {
  auto r = Parse("module t;\n"
                 "  int scores[string];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(item->unpacked_dims[0]->text, "string");
}

TEST(ParserSection7, AssocArrayIntIndex) {
  auto r = Parse("module t;\n"
                 "  byte lookup[int];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "lookup");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
}

TEST(ParserSection7, AssocArrayIntIndex_DimExpr) {
  auto r = Parse("module t;\n"
                 "  byte lookup[int];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(item->unpacked_dims[0]->text, "int");
}

TEST(ParserSection7, AssocArrayIntegerIndex) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] cache[integer];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cache");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(ParserSection7, AssocArrayIntegerIndex_DimExpr) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] cache[integer];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "integer");
}

// =========================================================================
// §7.10: Queues
// =========================================================================

TEST(ParserSection7, QueueUnbounded) {
  auto r = Parse("module t;\n"
                 "  byte q[$];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "q");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserSection7, QueueBounded) {
  auto r = Parse("module t;\n"
                 "  bit q2[$:255];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "q2");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// =========================================================================
// §7.12: Array manipulation methods
// =========================================================================

TEST(ParserSection7, ArrayMethodWithClause) {
  auto r = Parse("module t;\n"
                 "  initial qi = arr.find(x) with (x > 5);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_NE(rhs->with_expr, nullptr);
}

TEST(ParserSection7, ArrayMethodMin) {
  auto r = Parse("module t;\n"
                 "  initial y = arr.min;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  // min without parens is a member access
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, ArraySortWithClause) {
  auto r = Parse("module t;\n"
                 "  initial arr.sort with (item.x);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  // sort with no parens but with clause: member_access + with
  auto *expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
}

// =========================================================================
// §7.2.1: Packed structures (additional)
// =========================================================================

TEST(ParserSection7, StructPackedUnsigned) {
  auto r = Parse("module t;\n"
                 "  typedef struct packed unsigned {\n"
                 "    time a;\n"
                 "    integer b;\n"
                 "    logic [31:0] c;\n"
                 "  } pack2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_FALSE(item->typedef_type.is_signed);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 3u);
}

TEST(ParserSection7, StructMultipleMembersSameType) {
  auto r = Parse("module t;\n"
                 "  typedef struct {\n"
                 "    int x, y, z;\n"
                 "  } point;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  std::string expected_names[] = {"x", "y", "z"};
  ASSERT_EQ(item->typedef_type.struct_members.size(),
            std::size(expected_names));
  for (size_t i = 0; i < std::size(expected_names); ++i) {
    EXPECT_EQ(item->typedef_type.struct_members[i].name, expected_names[i])
        << "member " << i;
  }
}

// =========================================================================
// §7.2.2: Assigning to structures
// =========================================================================

TEST(ParserSection7, StructAssignmentPattern) {
  auto r = Parse("module t;\n"
                 "  typedef struct { int a; int b; } pair;\n"
                 "  initial begin\n"
                 "    pair p = '{1, 2};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  ASSERT_NE(stmt->var_init, nullptr);
  EXPECT_EQ(stmt->var_init->kind, ExprKind::kAssignmentPattern);
}

// =========================================================================
// §7.3.1: Packed unions
// =========================================================================

TEST(ParserSection7, UnionPacked) {
  auto r = Parse("module t;\n"
                 "  typedef union packed {\n"
                 "    logic [31:0] word;\n"
                 "    logic [3:0] [7:0] bytes;\n"
                 "  } word_u;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

// =========================================================================
// §7.3.2: Tagged unions (void members)
// =========================================================================

TEST(ParserSection7, TaggedUnionVoidMember) {
  auto r = Parse("module t;\n"
                 "  typedef union tagged {\n"
                 "    void Invalid;\n"
                 "    int Valid;\n"
                 "  } VInt;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
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
  auto r = Parse("module t;\n"
                 "  bit [3:0] [7:0] joe [1:10];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "joe");
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// =========================================================================
// §7.4.3: Memories
// =========================================================================

TEST(ParserSection7, MemoryDeclaration_Type) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] mema [0:255];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "mema");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(ParserSection7, MemoryDeclaration_Dim) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] mema [0:255];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto *dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->kind, ExprKind::kBinary);
  EXPECT_EQ(dim->op, TokenKind::kColon);
}

// =========================================================================
// §7.4.6: Operations on arrays
// =========================================================================

TEST(ParserSection7, ArrayAssignWhole) {
  auto r = Parse("module t;\n"
                 "  int a[4], b[4];\n"
                 "  initial a = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// =========================================================================
// §7.5.1: Dynamic array new[]
// =========================================================================

TEST(ParserSection7, DynamicArrayNew) {
  auto r = Parse("module t;\n"
                 "  int dyn[];\n"
                 "  initial dyn = new[10];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection7, DynamicArrayNewWithInit) {
  auto r = Parse("module t;\n"
                 "  int dyn[];\n"
                 "  int src[];\n"
                 "  initial dyn = new[20](src);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// =========================================================================
// §7.5.2/7.5.3: Dynamic array size() and delete()
// =========================================================================

TEST(ParserSection7, DynamicArraySizeMethod) {
  auto r = Parse("module t;\n"
                 "  int dyn[];\n"
                 "  initial x = dyn.size();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, DynamicArrayDeleteMethod) {
  auto r = Parse("module t;\n"
                 "  int dyn[];\n"
                 "  initial dyn.delete();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

// =========================================================================
// §7.6: Array assignments
// =========================================================================

TEST(ParserSection7, ArraySliceAssign) {
  auto r = Parse("module t;\n"
                 "  int a[8], b[8];\n"
                 "  initial a[3:0] = b[7:4];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

// =========================================================================
// §7.9: Associative array methods
// =========================================================================

TEST(ParserSection7, AssocArrayNumMethod) {
  auto r = Parse("module t;\n"
                 "  int aa[string];\n"
                 "  initial x = aa.num();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, AssocArrayExistsMethod) {
  auto r = Parse("module t;\n"
                 "  int aa[string];\n"
                 "  initial x = aa.exists(\"key\");\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, AssocArrayDeleteMethod) {
  auto r = Parse("module t;\n"
                 "  int aa[string];\n"
                 "  initial aa.delete(\"key\");\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

// =========================================================================
// §7.10.1: Queue operators
// =========================================================================

TEST(ParserSection7, QueueConcatAssign) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial q = {1, 2, 3};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

// =========================================================================
// §7.10.2: Queue methods
// =========================================================================

TEST(ParserSection7, QueuePushBack) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial q.push_back(42);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(ParserSection7, QueuePopFront) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial x = q.pop_front();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, QueueSizeMethod) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial x = q.size();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, QueueInsertMethod) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial q.insert(2, 99);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

// =========================================================================
// §7.11: Array querying functions
// =========================================================================

TEST(ParserSection7, ArrayDimensionsQuery) {
  auto r = Parse("module t;\n"
                 "  int arr[4][8];\n"
                 "  initial x = $dimensions(arr);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$dimensions");
}

TEST(ParserSection7, ArraySizeQuery) {
  auto r = Parse("module t;\n"
                 "  int arr[4];\n"
                 "  initial x = $size(arr);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$size");
}

// =========================================================================
// §7.12.1: Array locator methods
// =========================================================================

TEST(ParserSection7, ArrayFindWithClause) {
  auto r = Parse("module t;\n"
                 "  int d[] = '{1,2,3,4,5};\n"
                 "  initial qi = d.find with (item > 3);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
}

TEST(ParserSection7, ArrayFindIndexMethod) {
  auto r = Parse("module t;\n"
                 "  int arr[8];\n"
                 "  initial qi = arr.find_index with (item == 0);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

// =========================================================================
// §7.12.2: Array ordering methods
// =========================================================================

TEST(ParserSection7, ArrayReverseMethod) {
  auto r = Parse("module t;\n"
                 "  int arr[4];\n"
                 "  initial arr.reverse();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(ParserSection7, ArrayShuffleMethod) {
  auto r = Parse("module t;\n"
                 "  int arr[4];\n"
                 "  initial arr.shuffle();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

// =========================================================================
// §7.12.3: Array reduction methods
// =========================================================================

TEST(ParserSection7, ArraySumMethod) {
  auto r = Parse("module t;\n"
                 "  int arr[4];\n"
                 "  initial x = arr.sum;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, ArraySumWithClause) {
  auto r = Parse("module t;\n"
                 "  int arr[4];\n"
                 "  initial x = arr.sum with (item * 2);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection7, ArrayProductMethod) {
  auto r = Parse("module t;\n"
                 "  int arr[4];\n"
                 "  initial x = arr.product;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

// =========================================================================
// §7.12.5: Array mapping method
// =========================================================================

TEST(ParserSection7, ArrayMapMethod) {
  auto r = Parse("module t;\n"
                 "  int arr[4];\n"
                 "  initial qi = arr.map with (item + 1);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

// =========================================================================
// §7.4.5: Array indexing (element select)
// =========================================================================

TEST(ParserSection7, ArrayElementSelect) {
  auto r = Parse("module t;\n"
                 "  int arr[8];\n"
                 "  initial x = arr[3];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}

TEST(ParserSection7, MultiDimSelect) {
  auto r = Parse("module t;\n"
                 "  int arr[4][8];\n"
                 "  initial x = arr[2][5];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}
