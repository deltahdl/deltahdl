// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

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

static ModuleItem* NthItem(ParseResult7e& r, size_t n) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.size() <= n)
    return nullptr;
  return r.cu->modules[0]->items[n];
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

static Stmt* NthInitialStmt(ParseResult7e& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        if (item->body->stmts.size() > n) return item->body->stmts[n];
      }
      if (n == 0) return item->body;
    }
  }
  return nullptr;
}

namespace {

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

// =============================================================================
// LRM section 7.2.2 -- Assigning to structures
// =============================================================================
// 1. Named assignment pattern '{a: 1, b: 2}.
TEST(ParserSection7, Sec7_2_2_NamedAssignmentPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = '{a: 10, b: 20};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
  ASSERT_EQ(stmt->rhs->pattern_keys.size(), 2u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "a");
  EXPECT_EQ(stmt->rhs->pattern_keys[1], "b");
}

// 2. Default assignment pattern '{default: 0}.
TEST(ParserSection7, Sec7_2_2_DefaultAssignmentPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; int c; } triple_t;\n"
      "  triple_t t1;\n"
      "  initial t1 = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_GE(stmt->rhs->pattern_keys.size(), 1u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "default");
}

// 3. Named with default pattern '{a: 1, default: 0}.
TEST(ParserSection7, Sec7_2_2_NamedWithDefault) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; int c; } s_t;\n"
      "  s_t s;\n"
      "  initial s = '{a: 1, default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
  EXPECT_EQ(stmt->rhs->pattern_keys.size(), 2u);
}

// 4. Assignment pattern with replication '{4{8'h00}}.
TEST(ParserSection7, Sec7_2_2_ReplicationPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { byte a; byte b; byte c; byte d; } quad_t;\n"
      "  quad_t q;\n"
      "  initial q = '{4{8'h00}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
}

// 5. Struct variable assigned from another struct variable.
TEST(ParserSection7, Sec7_2_2_AssignFromStructVar) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  point_t a, b;\n"
      "  initial begin\n"
      "    a = '{1, 2};\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = NthInitialStmt(r, 1);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->text, "a");
}

// 6. Struct member assigned individually (s.a = 1).
TEST(ParserSection7, Sec7_2_2_MemberAssignment) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p.a = 10;\n"
      "    p.b = 20;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = NthInitialStmt(r, 0);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

// 7. Packed struct assigned from integer literal.
TEST(ParserSection7, Sec7_2_2_PackedStructFromInteger) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } word_t;\n"
      "  word_t w;\n"
      "  initial w = 16'hABCD;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kIntegerLiteral);
}

// 8. Packed struct assigned from concatenation.
TEST(ParserSection7, Sec7_2_2_PackedStructFromConcat) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  initial w = {8'hAB, 8'hCD};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

// 9. Default member values in struct typedef.
TEST(ParserSection7, Sec7_2_2_DefaultMemberValues) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    int addr = 32'h0;\n"
      "    int data = 32'hFF;\n"
      "    bit valid = 1'b0;\n"
      "  } pkt_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 3u);
  EXPECT_NE(item->typedef_type.struct_members[0].init_expr, nullptr);
  EXPECT_NE(item->typedef_type.struct_members[1].init_expr, nullptr);
  EXPECT_NE(item->typedef_type.struct_members[2].init_expr, nullptr);
}

// 10. Struct assigned in initial block with begin/end.
TEST(ParserSection7, Sec7_2_2_AssignInInitialBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } s_t;\n"
              "  s_t s;\n"
              "  initial begin\n"
              "    s = '{10, 20};\n"
              "  end\n"
              "endmodule\n"));
}

// 11. Struct assigned in always_comb block.
TEST(ParserSection7, Sec7_2_2_AssignInAlwaysComb) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic a; logic b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic sel;\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      p = '{1'b1, 1'b0};\n"
      "    else\n"
      "      p = '{1'b0, 1'b1};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 3);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
}

// 12. Struct assigned via continuous assign statement.
TEST(ParserSection7, Sec7_2_2_ContinuousAssign) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } s_t;\n"
      "  s_t s;\n"
      "  assign s = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 2);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  ASSERT_NE(item->assign_lhs, nullptr);
  ASSERT_NE(item->assign_rhs, nullptr);
}

// 13. Struct as function return value.
TEST(ParserSection7, Sec7_2_2_FunctionReturnStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  function point_t make_point;\n"
      "    input int a, b;\n"
      "    make_point = '{a, b};\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 1);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
}

// 14. Struct as function argument.
TEST(ParserSection7, Sec7_2_2_FunctionArgStruct) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  function int sum_pair;\n"
              "    input pair_t p;\n"
              "    sum_pair = p.a + p.b;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// 15. Nested struct assignment pattern.
TEST(ParserSection7, Sec7_2_2_NestedStructPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  typedef struct { point_t origin; point_t size; } rect_t;\n"
      "  rect_t r1;\n"
      "  initial r1 = '{'{0, 0}, '{10, 20}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->elements.size(), 2u);
  EXPECT_EQ(stmt->rhs->elements[0]->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements[1]->kind, ExprKind::kAssignmentPattern);
}

}  // namespace
