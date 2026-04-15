#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PackedStructParsing, TypedefStructPacked) {
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

TEST(PackedStructParsing, PackedSignedVarDecl) {
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

TEST(PackedStructParsing, PackedTypedefLogicWidths) {
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

TEST(PackedStructParsing, PackedTypedefBitMembers) {
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

TEST(PackedStructParsing, PackedIntegerTypes) {
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

TEST(PackedStructParsing, PackedSignedTypedef) {
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

TEST(PackedStructParsing, PackedVarDecl) {
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

static ModuleItem* NthItem(ParseResult& r, size_t n) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.size() <= n)
    return nullptr;
  return r.cu->modules[0]->items[n];
}

TEST(PackedStructParsing, PackedVarWithInit) {
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

TEST(PackedStructParsing, PackedMemberAccessRead) {
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
TEST(PackedStructParsing, PackedMemberAccessWrite) {
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
TEST(PackedStructParsing, StructPackedSigned) {
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

TEST(PackedStructParsing, PackedStructBitwise) {
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

TEST(PackedStructParsing, PackedAssignFromConcat) {
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

TEST(PackedStructParsing, StructMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] addr;\n"
      "    logic [7:0] data;\n"
      "  } pkt_t;\n"
      "  pkt_t pkt;\n"
      "  logic [7:0] a, d;\n"
      "  always_comb begin\n"
      "    pkt.addr = a;\n"
      "    pkt.data = d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);

  EXPECT_EQ(item->body->stmts[0]->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(item->body->stmts[1]->lhs->kind, ExprKind::kMemberAccess);
}

TEST(PackedStructParsing, PackedWithPackedArrayMember) {
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

TEST(PackedStructParsing, PackedMemberMultiPackedDims) {
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

TEST(PackedStructParsing, StructOutputPort) {
  EXPECT_TRUE(
      ParseOk("module t(\n"
              "  output logic [15:0] result\n"
              ");\n"
              "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
              "  s_t s;\n"
              "  assign s = 16'hDEAD;\n"
              "  assign result = s;\n"
              "endmodule\n"));
}

TEST(PackedStructParsing, NestedPackedStruct) {
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

TEST(PackedStructParsing, PackedStructWithPackedUnion) {
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

TEST(PackedStructParsing, PackedStructAssignToLogicVector) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] upper;\n"
      "    logic [3:0] lower;\n"
      "  } nibbles_t;\n"
      "  nibbles_t n;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    n = 8'b1010_0101;\n"
      "    result = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  ASSERT_NE(s0, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(s0->rhs, nullptr);
  EXPECT_EQ(s0->rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(PackedStructParsing, PackedWithEnumMember) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef enum logic [1:0] { IDLE, RUN, STOP } state_e;\n"
              "  typedef struct packed {\n"
              "    state_e state;\n"
              "    logic [5:0] data;\n"
              "  } ctrl_t;\n"
              "endmodule\n"));
}

TEST(PackedStructParsing, PackedInPackage) {
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

TEST(PackedStructParsing, TypedefUsedInVarDecl) {
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

TEST(PackedStructParsing, PackedSingleBitMember) {
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

TEST(PackedStructParsing, StructPackedUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed unsigned {\n"
      "    time a;\n"
      "    integer b;\n"
      "    logic [31:0] c;\n"
      "  } pack2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_FALSE(item->typedef_type.is_signed);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 3u);
}

TEST(PackedStructParsing, PackedMemberSignedType) {
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

TEST(PackedStructParsing, AtmCellHeader) {
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

TEST(PackedStructParsing, PackedMultiMembersSameType) {
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

TEST(PackedStructParsing, PackedStructFromInteger) {
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

TEST(PackedStructParsing, PackedSignedAllTwoStateMembers) {
  auto r = Parse(
      "module t;\n"
      "  struct packed signed {\n"
      "    int a;\n"
      "    shortint b;\n"
      "    byte c;\n"
      "    bit [7:0] d;\n"
      "  } pack1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->data_type.struct_members.size(), 4u);
}

TEST(PackedStructParsing, PackedUnsignedWithFourStateMembers) {
  auto r = Parse(
      "module t;\n"
      "  struct packed unsigned {\n"
      "    time a;\n"
      "    integer b;\n"
      "    logic [31:0] c;\n"
      "  } pack2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->data_type.struct_members.size(), 3u);
}

TEST(PackedStructParsing, PackedStructDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    bit [3:0] x;\n"
      "  } ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_FALSE(item->data_type.is_signed);
}

TEST(PackedStructParsing, PackedStructPartSelect) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    bit [7:0] a;\n"
      "    bit [7:0] b;\n"
      "  } s;\n"
      "  initial x = s[15:8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}

TEST(PackedStructParsing, PackedStructBasicDecl) {
  auto r = Parse(
      "module m;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
