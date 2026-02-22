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
  CompilationUnit *cu = nullptr;
};

static ParseResult7b Parse(const std::string &src) {
  ParseResult7b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem *FirstItem(ParseResult7b &r) {
  if (!r.cu || r.cu->modules.empty())
    return nullptr;
  auto &items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt *FirstInitialStmt(ParseResult7b &r) {
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
// §7.4: Struct variable declaration (non-typedef)
// =========================================================================

TEST(ParserSection7, StructVariableDecl) {
  auto r = Parse("module t;\n"
                 "  struct { int a; int b; } my_var;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_EQ(item->name, "my_var");
}

// =========================================================================
// §7.12.1: Array locator method 'unique' (keyword as method name)
// =========================================================================

TEST(ParserSection7, ArrayLocatorUnique) {
  auto r = Parse("module t;\n"
                 "  int s[] = '{10, 10, 3, 20, 20, 10};\n"
                 "  int qi[$];\n"
                 "  initial qi = s.unique;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

// =========================================================================
// §7.12.3: Array reduction methods 'and', 'or', 'xor' (keywords as names)
// =========================================================================

TEST(ParserSection7, ArrayReductionAnd) {
  auto r = Parse("module t;\n"
                 "  byte b[] = '{1, 3, 5, 7};\n"
                 "  initial y = b.and;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, ArrayReductionOr) {
  auto r = Parse("module t;\n"
                 "  byte b[] = '{1, 2, 3, 4};\n"
                 "  initial y = b.or;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, ArrayReductionXor) {
  auto r = Parse("module t;\n"
                 "  byte b[] = '{1, 2, 3, 4};\n"
                 "  initial y = b.xor;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

// =========================================================================
// §7.10.4: Empty concatenation {} to clear queue
// =========================================================================

TEST(ParserSection7, EmptyConcatClearQueue_Parse) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial q = {};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection7, EmptyConcatClearQueue_Rhs) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial q = {};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_TRUE(stmt->rhs->elements.empty());
}

TEST(ParserSection7, UnionWithNestedStruct) {
  auto r = Parse("module t;\n"
                 "  typedef union tagged {\n"
                 "    struct {\n"
                 "      bit [4:0] reg1, reg2;\n"
                 "    } Add;\n"
                 "    bit [9:0] Jmp;\n"
                 "  } Instr;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

// =========================================================================
// §7.12: Array manipulation methods (additional tests)
// =========================================================================

TEST(ParserSection7, ArrayLocatorFindWithClause) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{1, 2, 3, 4, 5};\n"
                 "  int found[$];\n"
                 "  initial found = arr.find with (item > 3);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection7, ArrayLocatorFindIndex) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{10, 20, 30};\n"
                 "  int idx[$];\n"
                 "  initial idx = arr.find_index with (item == 20);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection7, ArrayMethodSort) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{5, 3, 1, 4, 2};\n"
                 "  initial arr.sort;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection7, ArrayMethodRsort) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{1, 2, 3, 4, 5};\n"
                 "  initial arr.rsort;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection7, ArrayMethodShuffle) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{1, 2, 3};\n"
                 "  initial arr.shuffle;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection7, ArrayReductionSum) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{1, 2, 3};\n"
                 "  initial y = arr.sum;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

// =========================================================================
// §7.10: Queues (additional tests)
// =========================================================================

TEST(ParserSection7, QueueDeclaration) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "q");
}

TEST(ParserSection7, QueueWithBound) {
  auto r = Parse("module t;\n"
                 "  bit q2[$:255];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "q2");
}

TEST(ParserSection7, QueueWithInitializer) {
  auto r = Parse("module t;\n"
                 "  integer Q[$] = '{3, 2, 7};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "Q");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection7, QueueMethodPushBack) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial q.push_back(42);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection7, QueueMethodSize) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial y = q.size;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

// =========================================================================
// §7.8: Associative arrays
// =========================================================================

TEST(ParserSection7, AssociativeArrayWildcardIndex) {
  auto r = Parse("module t;\n"
                 "  int aa[*];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "aa");
}

TEST(ParserSection7, AssociativeArrayTypedIndex) {
  auto r = Parse("module t;\n"
                 "  int aa[string];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "aa");
}

TEST(ParserSection7, AssociativeArrayIntIndex) {
  auto r = Parse("module t;\n"
                 "  string names[int];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "names");
}

// =========================================================================
// §7.4: Packed arrays — multi-dimensional packed declaration
// =========================================================================

TEST(ParserSection7, PackedArrayMultiDim) {
  auto r = Parse("module t;\n"
                 "  bit [3:0][7:0] packed_2d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "packed_2d");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
}

TEST(ParserSection7, PackedArrayWithUnpacked) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] mem [0:255];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "mem");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserSection7, UnpackedArrayFixedSize) {
  auto r = Parse("module t;\n"
                 "  int arr [3];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// =========================================================================
// §7.4.5: Dynamic arrays — declaration and new
// =========================================================================

TEST(ParserSection7, DynamicArrayDecl) {
  auto r = Parse("module t;\n"
                 "  bit [3:0] nibble[];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "nibble");
}

TEST(ParserSection7, DynamicArrayNew) {
  auto r = Parse("module t;\n"
                 "  int dyn[];\n"
                 "  initial dyn = new[10];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection7, DynamicArrayMultiDim) {
  auto r = Parse("module t;\n"
                 "  integer mem[2][];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "mem");
}

// =========================================================================
// §7.7: Queues — additional declaration forms
// =========================================================================

TEST(ParserSection7, QueueOfStrings) {
  auto r = Parse("module t;\n"
                 "  string names[$] = '{\"Bob\"};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "names");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection7, QueuePushFront) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial q.push_front(99);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection7, QueuePopBack) {
  auto r = Parse("module t;\n"
                 "  int q[$] = '{1, 2, 3};\n"
                 "  initial y = q.pop_back();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

// =========================================================================
// §7.10: Array manipulation methods — min, max, unique_index
// =========================================================================

TEST(ParserSection7, ArrayMethodMin) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{5, 1, 3};\n"
                 "  int res[$];\n"
                 "  initial res = arr.min;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, ArrayMethodMax) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{5, 1, 3};\n"
                 "  int res[$];\n"
                 "  initial res = arr.max;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, ArrayMethodUniqueIndex) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{1, 2, 1, 3};\n"
                 "  int idx[$];\n"
                 "  initial idx = arr.unique_index;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

// =========================================================================
// §7.10.4: Array ordering methods — reverse
// =========================================================================

TEST(ParserSection7, ArrayMethodReverse) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{1, 2, 3};\n"
                 "  initial arr.reverse;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection7, ArraySortWithClause) {
  auto r = Parse("module t;\n"
                 "  typedef struct { int x; int y; } point_t;\n"
                 "  point_t pts[];\n"
                 "  initial pts.sort with (item.x);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

// =========================================================================
// §7.12: Array assignment patterns — replication, default, keyed
// =========================================================================

TEST(ParserSection7, AssignmentPatternReplication) {
  auto r = Parse("module t;\n"
                 "  int A[8] = '{2{1, 2, 3, 4}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection7, AssignmentPatternDefault) {
  auto r = Parse("module t;\n"
                 "  int B[4] = '{default:0};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection7, AssignmentPatternPositional) {
  auto r = Parse("module t;\n"
                 "  int C[3] = '{10, 20, 30};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
}

// =========================================================================
// §7.2.1: Packed structures
// =========================================================================

TEST(ParserSection7, PackedStructSigned2State) {
  auto r = Parse("module t;\n"
                 "  struct packed signed {\n"
                 "    int a;\n"
                 "    shortint b;\n"
                 "    byte c;\n"
                 "    bit [7:0] d;\n"
                 "  } pack1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->data_type.struct_members.size(), 4u);
}

TEST(ParserSection7, PackedStructUnsigned4State) {
  auto r = Parse("module t;\n"
                 "  struct packed unsigned {\n"
                 "    time a;\n"
                 "    integer b;\n"
                 "    logic [31:0] c;\n"
                 "  } pack2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->data_type.struct_members.size(), 3u);
}

TEST(ParserSection7, PackedStructDefaultUnsigned) {
  auto r = Parse("module t;\n"
                 "  struct packed {\n"
                 "    bit [3:0] x;\n"
                 "  } ps;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_FALSE(item->data_type.is_signed);
}

TEST(ParserSection7, PackedStructWithTypedef) {
  auto r = Parse("module t;\n"
                 "  typedef struct packed {\n"
                 "    bit [3:0] GFC;\n"
                 "    bit [7:0] VPI;\n"
                 "    bit [11:0] VCI;\n"
                 "    bit CLP;\n"
                 "    bit [3:0] PT;\n"
                 "    bit [7:0] HEC;\n"
                 "  } s_atmcell;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 6u);
}

TEST(ParserSection7, PackedStructPartSelect) {
  auto r = Parse("module t;\n"
                 "  struct packed {\n"
                 "    bit [7:0] a;\n"
                 "    bit [7:0] b;\n"
                 "  } s;\n"
                 "  initial x = s[15:8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}

// =========================================================================
// §7.2.2: Assigning to structures
// =========================================================================

TEST(ParserSection7, StructWholeAssignment) {
  auto r = Parse("module t;\n"
                 "  typedef struct { int a; int b; } pair_t;\n"
                 "  pair_t p1, p2;\n"
                 "  initial p2 = p1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection7, StructMemberDefaultInit) {
  auto r = Parse("module t;\n"
                 "  typedef struct {\n"
                 "    int addr = 100;\n"
                 "    int crc;\n"
                 "    byte data [4] = '{4{1}};\n"
                 "  } packet1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 3u);
  EXPECT_NE(item->typedef_type.struct_members[0].init_expr, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members[1].init_expr, nullptr);
  EXPECT_NE(item->typedef_type.struct_members[2].init_expr, nullptr);
}

TEST(ParserSection7, StructAssignmentPattern) {
  auto r = Parse("module t;\n"
                 "  typedef struct { int a; int b; } pair_t;\n"
                 "  pair_t p;\n"
                 "  initial p = '{10, 20};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

TEST(ParserSection7, UnpackedStructDecl) {
  auto r = Parse("module t;\n"
                 "  struct {\n"
                 "    int x;\n"
                 "    real y;\n"
                 "    string s;\n"
                 "  } my_unpacked;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_FALSE(item->data_type.is_packed);
  EXPECT_EQ(item->data_type.struct_members.size(), 3u);
}

TEST(ParserSection7, UnpackedStructTypedefDecl) {
  auto r = Parse("module t;\n"
                 "  typedef struct {\n"
                 "    int addr;\n"
                 "    int crc;\n"
                 "    byte data [4];\n"
                 "  } packet;\n"
                 "  packet p;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_FALSE(item->typedef_type.is_packed);
}

TEST(ParserSection7, StructMemberAccess) {
  auto r = Parse("module t;\n"
                 "  struct { int x; int y; } s;\n"
                 "  initial s.x = 42;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}
