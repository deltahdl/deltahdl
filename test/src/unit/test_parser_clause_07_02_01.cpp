// §7.2.1: Packed structures

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2TypedefStructPacked) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] addr;\n"
      "    logic [31:0] data;\n"
      "  } req_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

// struct_union [packed [signing]] { ... } {packed_dimension}
TEST(ParserA221, DataTypeStructPacked) {
  auto r = Parse(
      "module m;\n"
      "  struct packed signed { logic [7:0] a; logic [7:0] b; } pair;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_TRUE(item->data_type.is_signed);
}

struct ParseResult7e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7e Parse(const std::string& src) {
  ParseResult7e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult7e& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// =========================================================================
// LRM section 7.2.1 -- Packed structures
// =========================================================================
// --- Packed struct typedef with logic members of various widths ---
TEST(ParserSection7, Sec7_2_1_PackedTypedefLogicWidths) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [15:0] addr;\n"
      "    logic [7:0] data;\n"
      "    logic valid;\n"
      "  } bus_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_FALSE(item->typedef_type.is_signed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 3u);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "addr");
  EXPECT_EQ(item->typedef_type.struct_members[1].name, "data");
  EXPECT_EQ(item->typedef_type.struct_members[2].name, "valid");
}

// --- Packed struct typedef with bit members and packed dim checks ---
TEST(ParserSection7, Sec7_2_1_PackedTypedefBitMembers) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    bit [3:0] nibble_hi;\n"
      "    bit [3:0] nibble_lo;\n"
      "  } byte_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_EQ(item->typedef_type.struct_members[0].type_kind, DataTypeKind::kBit);
  EXPECT_EQ(item->typedef_type.struct_members[1].type_kind, DataTypeKind::kBit);
  EXPECT_NE(item->typedef_type.struct_members[0].packed_dim_left, nullptr);
  EXPECT_NE(item->typedef_type.struct_members[0].packed_dim_right, nullptr);
}

// --- Packed struct with integer type members (byte, shortint, int, longint)
// ---
TEST(ParserSection7, Sec7_2_1_PackedIntegerTypes) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    byte a;\n"
      "    shortint b;\n"
      "    int c;\n"
      "    longint d;\n"
      "  } wide_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 4u);
  EXPECT_EQ(item->typedef_type.struct_members[0].type_kind,
            DataTypeKind::kByte);
  EXPECT_EQ(item->typedef_type.struct_members[1].type_kind,
            DataTypeKind::kShortint);
  EXPECT_EQ(item->typedef_type.struct_members[2].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(item->typedef_type.struct_members[3].type_kind,
            DataTypeKind::kLongint);
}

// --- Packed struct signed typedef with member name verification ---
TEST(ParserSection7, Sec7_2_1_PackedSignedTypedef) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed signed {\n"
      "    logic [15:0] real_part;\n"
      "    logic [15:0] imag_part;\n"
      "  } complex_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_TRUE(item->typedef_type.is_signed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "real_part");
  EXPECT_EQ(item->typedef_type.struct_members[1].name, "imag_part");
}

// --- Packed struct variable declaration (non-typedef, inline) ---
TEST(ParserSection7, Sec7_2_1_PackedVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    logic [7:0] tag;\n"
      "    logic [23:0] payload;\n"
      "  } pkt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_EQ(item->name, "pkt");
  EXPECT_EQ(item->data_type.struct_members.size(), 2u);
}

static ModuleItem* NthItem(ParseResult7e& r, size_t n) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.size() <= n)
    return nullptr;
  return r.cu->modules[0]->items[n];
}

// --- Packed struct variable with initial value ---
TEST(ParserSection7, Sec7_2_1_PackedVarWithInit) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    bit [7:0] hi;\n"
      "    bit [7:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t p = 16'hABCD;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 1);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "p");
  EXPECT_NE(item->init_expr, nullptr);
}

static Stmt* FirstInitialStmt(ParseResult7e& r) {
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

// --- Packed struct member access via dot notation on RHS ---
TEST(ParserSection7, Sec7_2_1_PackedMemberAccessRead) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "  } s;\n"
      "  initial x = s.a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

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

TEST(Parser, TypedefStructPacked) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } byte_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2);
}

// --- Packed struct member access on LHS ---
TEST(ParserSection7, Sec7_2_1_PackedMemberAccessWrite) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    logic [7:0] hi;\n"
      "    logic [7:0] lo;\n"
      "  } s;\n"
      "  initial s.hi = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

static ModuleItem* FirstItem(ParseResult7& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

TEST(ParserSection7, StructPackedSigned) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed signed {\n"
      "    int a;\n"
      "    byte b;\n"
      "  } packed_s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_TRUE(item->typedef_type.is_signed);
}

// 21. Packed struct bitwise operations.
TEST(ParserSection7, Sec7_2_2_PackedStructBitwise) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } w_t;\n"
      "  w_t x, y, z;\n"
      "  initial z = x & y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kAmp);
}

// --- Packed struct assigned from concatenation ---
TEST(ParserSection7, Sec7_2_1_PackedAssignFromConcat) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] hi;\n"
      "    logic [7:0] lo;\n"
      "  } word_t;\n"
      "  word_t w;\n"
      "  initial w = {8'hAB, 8'hCD};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

}  // namespace
