#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult7d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7d Parse(const std::string& src) {
  ParseResult7d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FirstItem(ParseResult7d& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static ModuleItem* NthItem(ParseResult7d& r, size_t n) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return n < items.size() ? items[n] : nullptr;
}

static Stmt* FirstInitialStmt(ParseResult7d& r) {
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

// --- Packed struct bit-select ---

TEST(ParserSection7, Sec7_2_1_PackedBitSelect) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    bit [7:0] a;\n"
      "    bit [7:0] b;\n"
      "  } s;\n"
      "  initial x = s[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
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

// --- Packed struct assigned from assignment pattern ---

TEST(ParserSection7, Sec7_2_1_PackedAssignFromPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] opcode;\n"
      "    logic [7:0] data;\n"
      "  } cmd_t;\n"
      "  cmd_t c;\n"
      "  initial c = '{8'h01, 8'hFF};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

// --- Packed struct as function return type ---

TEST(ParserSection7, Sec7_2_1_PackedAsFuncReturn) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] a;\n"
              "    logic [7:0] b;\n"
              "  } pair_t;\n"
              "  function pair_t make_pair;\n"
              "    input logic [7:0] x, y;\n"
              "    make_pair = {x, y};\n"
              "  endfunction\n"
              "endmodule\n"));
}

// --- Packed struct as port type (inline struct in port list) ---

TEST(ParserSection7, Sec7_2_1_PackedAsPortType) {
  EXPECT_TRUE(ParseOk(
      "module inner(\n"
      "  input struct packed { logic [7:0] a; logic [7:0] b; } data_in,\n"
      "  output logic [15:0] data_out\n"
      ");\n"
      "  assign data_out = data_in;\n"
      "endmodule\n"));
}

// --- Packed struct with packed array member (extra_packed_dims) ---

TEST(ParserSection7, Sec7_2_1_PackedWithPackedArrayMember) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0][7:0] bytes;\n"
      "    logic [31:0] word;\n"
      "  } frame_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "bytes");
  EXPECT_NE(item->typedef_type.struct_members[0].packed_dim_left, nullptr);
  EXPECT_FALSE(item->typedef_type.struct_members[0].extra_packed_dims.empty());
}

// --- Packed struct with multiple packed dimensions on a member ---

TEST(ParserSection7, Sec7_2_1_PackedMemberMultiPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    bit [1:0][3:0][7:0] data;\n"
      "  } multi_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 1u);
  auto& member = item->typedef_type.struct_members[0];
  EXPECT_EQ(member.name, "data");
  EXPECT_NE(member.packed_dim_left, nullptr);
  EXPECT_NE(member.packed_dim_right, nullptr);
  EXPECT_GE(member.extra_packed_dims.size(), 1u);
}

// --- Nested packed struct (packed struct inside packed struct) ---

TEST(ParserSection7, Sec7_2_1_NestedPackedStruct) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct packed {\n"
              "    struct packed {\n"
              "      logic [7:0] x;\n"
              "      logic [7:0] y;\n"
              "    } coord;\n"
              "    logic [7:0] color;\n"
              "  } pixel_t;\n"
              "endmodule\n"));
}

// --- Packed struct containing packed union ---

TEST(ParserSection7, Sec7_2_1_PackedStructWithPackedUnion) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] tag;\n"
              "    union packed {\n"
              "      logic [31:0] word;\n"
              "      logic [3:0][7:0] bytes;\n"
              "    } payload;\n"
              "  } tagged_data_t;\n"
              "endmodule\n"));
}

// --- Packed struct with enum member (named type) ---

TEST(ParserSection7, Sec7_2_1_PackedWithEnumMember) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef enum logic [1:0] { IDLE, RUN, STOP } state_e;\n"
              "  typedef struct packed {\n"
              "    state_e state;\n"
              "    logic [5:0] data;\n"
              "  } ctrl_t;\n"
              "endmodule\n"));
}

// --- Packed struct typedef in a package ---

TEST(ParserSection7, Sec7_2_1_PackedInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] addr;\n"
      "    logic [7:0] data;\n"
      "  } pkt_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_FALSE(r.cu->packages[0]->items.empty());
  auto* item = r.cu->packages[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

// --- Cast packed struct to integer type ---

TEST(ParserSection7, Sec7_2_1_PackedCastToInt) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [15:0] a;\n"
      "    logic [15:0] b;\n"
      "  } wide_t;\n"
      "  wide_t w;\n"
      "  initial x = int'(w);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

// --- Cast integer to packed struct type ---

TEST(ParserSection7, Sec7_2_1_IntCastToPackedStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] hi;\n"
      "    logic [7:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = pair_t'(16'hBEEF);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

// --- Packed struct typedef used in subsequent variable declaration ---

TEST(ParserSection7, Sec7_2_1_TypedefUsedInVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "  } pair_t;\n"
      "  pair_t my_pair;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 1);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "my_pair");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "pair_t");
}

// --- Packed struct with single-bit member (no packed dimension) ---

TEST(ParserSection7, Sec7_2_1_PackedSingleBitMember) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    bit [6:0] data;\n"
      "    bit parity;\n"
      "  } frame_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  auto& parity = item->typedef_type.struct_members[1];
  EXPECT_EQ(parity.name, "parity");
  EXPECT_EQ(parity.type_kind, DataTypeKind::kBit);
  EXPECT_EQ(parity.packed_dim_left, nullptr);
  EXPECT_EQ(parity.packed_dim_right, nullptr);
}

// --- Packed struct with signed member type qualifier ---

TEST(ParserSection7, Sec7_2_1_PackedMemberSignedType) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic signed [7:0] value;\n"
      "    logic [7:0] magnitude;\n"
      "  } signed_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_TRUE(item->typedef_type.struct_members[0].is_signed);
  EXPECT_FALSE(item->typedef_type.struct_members[1].is_signed);
}

// --- Packed struct indexed part-select plus ---

TEST(ParserSection7, Sec7_2_1_PackedIndexedPartSelectPlus) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    bit [7:0] a;\n"
      "    bit [7:0] b;\n"
      "    bit [7:0] c;\n"
      "    bit [7:0] d;\n"
      "  } s;\n"
      "  initial x = s[8 +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->rhs->is_part_select_plus);
}

// --- Packed struct indexed part-select minus ---

TEST(ParserSection7, Sec7_2_1_PackedIndexedPartSelectMinus) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    bit [7:0] a;\n"
      "    bit [7:0] b;\n"
      "    bit [7:0] c;\n"
      "    bit [7:0] d;\n"
      "  } s;\n"
      "  initial x = s[23 -: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->rhs->is_part_select_minus);
}

// --- ATM cell header: LRM-style packed struct with many fields ---

TEST(ParserSection7, Sec7_2_1_AtmCellHeader) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    bit [3:0] GFC;\n"
      "    bit [7:0] VPI;\n"
      "    bit [11:0] VCI;\n"
      "    bit CLP;\n"
      "    bit [3:0] PT;\n"
      "    bit [7:0] HEC;\n"
      "    bit [47:0][7:0] Payload;\n"
      "  } s_atmcell;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 7u);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "GFC");
  EXPECT_EQ(item->typedef_type.struct_members[3].name, "CLP");
  EXPECT_EQ(item->typedef_type.struct_members[6].name, "Payload");
}

// --- Packed struct with member default initializer ---

TEST(ParserSection7, Sec7_2_1_PackedMemberDefaultInit) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] cmd = 8'h00;\n"
      "    logic [7:0] data;\n"
      "  } msg_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_NE(item->typedef_type.struct_members[0].init_expr, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members[1].init_expr, nullptr);
}

// --- Packed struct with multiple members of the same type (comma-separated)
// ---

TEST(ParserSection7, Sec7_2_1_PackedMultiMembersSameType) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    bit [7:0] r, g, b;\n"
      "  } rgb_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 3u);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "r");
  EXPECT_EQ(item->typedef_type.struct_members[1].name, "g");
  EXPECT_EQ(item->typedef_type.struct_members[2].name, "b");
}

// --- Packed struct continuous assignment ---

TEST(ParserSection7, Sec7_2_1_PackedContAssign) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] a;\n"
              "    logic [7:0] b;\n"
              "  } pair_t;\n"
              "  pair_t p;\n"
              "  assign p = 16'h1234;\n"
              "endmodule\n"));
}
