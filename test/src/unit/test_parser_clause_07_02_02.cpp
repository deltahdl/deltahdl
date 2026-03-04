// §7.2.2: Assigning to structures

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection7, StructMemberInit) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    int addr = 100;\n"
      "    int crc;\n"
      "  } packet;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_NE(item->typedef_type.struct_members[0].init_expr, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members[1].init_expr, nullptr);
}

// 23. Struct variable declaration with initializer in initial block.
TEST(ParserSection7, Sec7_2_2_VarDeclWithInit) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p = '{5, 10};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_name, "p");
  ASSERT_NE(stmt->var_init, nullptr);
  EXPECT_EQ(stmt->var_init->kind, ExprKind::kAssignmentPattern);
}

// 25. Struct with packed array member assigned.
TEST(ParserSection7, Sec7_2_2_PackedArrayMemberAssign) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    logic [7:0] data;\n"
      "    logic [3:0] tag;\n"
      "  } tagged_data_t;\n"
      "  tagged_data_t td;\n"
      "  initial begin\n"
      "    td.data = 8'hFF;\n"
      "    td.tag = 4'hA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(s1->lhs->kind, ExprKind::kMemberAccess);
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
// --- Test helpers ---
// =========================================================================
// §7.2.2: Assigning to structures
// =========================================================================
TEST(ParserSection7, StructWholeAssignment) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p1, p2;\n"
      "  initial p2 = p1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}
TEST(ParserSection7, StructMemberDefaultInit) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    int addr = 100;\n"
      "    int crc;\n"
      "    byte data [4] = '{4{1}};\n"
      "  } packet1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 3u);
  EXPECT_NE(item->typedef_type.struct_members[0].init_expr, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members[1].init_expr, nullptr);
  EXPECT_NE(item->typedef_type.struct_members[2].init_expr, nullptr);
}

}  // namespace
