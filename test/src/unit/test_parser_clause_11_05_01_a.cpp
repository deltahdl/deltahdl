#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(OperatorAndExpressionParsing, BitSelectConstantIndex) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] vec;\n"
      "  initial x = vec[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

TEST(OperatorAndExpressionParsing, BitSelectVariableIndex) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] vec;\n"
      "  initial x = vec[idx];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, BitSelectExpressionIndex) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] vec;\n"
      "  initial x = vec[a + b];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->index->op, TokenKind::kPlus);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(AssignmentParsing, PartSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a[7:4] = 4'hF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->lhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, ConstPartSelectDescending) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] vec;\n"
      "  initial x = vec[7:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

TEST(OperatorAndExpressionParsing, ConstPartSelectAscending) {
  auto r = Parse(
      "module t;\n"
      "  logic [0:15] vec;\n"
      "  initial x = vec[0:7];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

TEST(OperatorAndExpressionParsing, IndexedPartSelectUpVariableBase) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  initial x = vec[offset +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_EQ(rhs->index_end->kind, ExprKind::kIntegerLiteral);
}

TEST(OperatorAndExpressionParsing, IndexedPartSelectDownVariableBase) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  initial x = vec[offset -: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
  EXPECT_FALSE(rhs->is_part_select_plus);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index_end, nullptr);
}

TEST(ProcessParsing, BitSelectLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic val;\n"
      "  always_comb data[3] = val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kSelect);
}

TEST(PrimaryParsing, RangeExpressionSimpleIndex) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial x = data[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(PrimaryParsing, RangeExpressionPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[7:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index_end, nullptr);
}

TEST(AggregateTypeParsing, PackedBitSelect) {
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

TEST(ProcessParsing, PartSelectLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] bus;\n"
      "  logic [7:0] low_byte;\n"
      "  always_comb bus[7:0] = low_byte;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kSelect);
  EXPECT_NE(item->body->lhs->index, nullptr);
  EXPECT_NE(item->body->lhs->index_end, nullptr);
}
static Expr* FirstAssignLhs(ParseResult& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->lhs;
}

TEST(OperatorAndExpressionParsing, PartSelectOnLhsBlocking) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] vec;\n"
      "  initial vec[7:0] = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* lhs = FirstAssignLhs(r);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kSelect);
  ASSERT_NE(lhs->index, nullptr);
  ASSERT_NE(lhs->index_end, nullptr);
  EXPECT_FALSE(lhs->is_part_select_plus);
  EXPECT_FALSE(lhs->is_part_select_minus);
}

TEST(OperatorAndExpressionParsing, IndexedPartSelectOnLhs) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  initial vec[i +: 4] = 4'hA;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* lhs = FirstAssignLhs(r);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(lhs->is_part_select_plus);
  ASSERT_NE(lhs->index, nullptr);
  ASSERT_NE(lhs->index_end, nullptr);
}

static ModuleItem* FirstContAssign(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

TEST(OperatorAndExpressionParsing, PartSelectInContAssignRhs) {
  auto r = Parse(
      "module t;\n"
      "  wire [15:0] data;\n"
      "  wire [7:0] low;\n"
      "  assign low = data[7:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_rhs->index, nullptr);
  ASSERT_NE(ca->assign_rhs->index_end, nullptr);
}

TEST(ExpressionParsing, ConstantRangeExprBitSelect) {
  auto r = Parse("module m; initial x = data[3]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(ExpressionParsing, ConstantRangePartSelect) {
  auto r = Parse("module m; initial x = data[7:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}
TEST(AggregateTypeParsing, IndexedPartSelectPlus) {
  auto r = Parse(
      "module t;\n"
      "  initial x = data[3 +: 4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

TEST(AggregateTypeParsing, IndexedPartSelectMinus) {
  auto r = Parse(
      "module t;\n"
      "  initial x = data[7 -: 4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

TEST(ExpressionParsing, IndexedRangePlusColon) {
  auto r = Parse("module m; initial x = data[2+:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

TEST(ExpressionParsing, IndexedRangeMinusColon) {
  auto r = Parse("module m; initial x = data[7-:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

TEST(OperatorAndExpressionParsing, PartSelectAfterBitSelect) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] [7:0] packed_arr;\n"
      "  initial x = packed_arr[1][7:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->base->index_end, nullptr);
}

TEST(ExpressionParsing, IndexedRangeVariableBase) {
  auto r = Parse("module m; initial x = data[i+:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
}

TEST(OperatorAndExpressionParsing, BitSelectOnConcat) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a, b, c;\n"
      "  initial a = {b, c}[5:2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, SelectOnMemberAccess) {
  auto r = Parse(
      "module t;\n"
      "  initial x = s.field[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, IndexedPartSelectInAlwaysComb) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] out;\n"
      "  always_comb out = vec[8 +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysCombItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(item->body->rhs->is_part_select_plus);
}

TEST(FormalSyntaxParsing, BitAndPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = data[3]; y = data[7:4]; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, PartSelectWithSysFuncIndex) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  initial x = vec[$clog2(16):0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kSystemCall);
  ASSERT_NE(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, MultiplePartSelectsInExpr) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  initial x = a[7:0] | b[15:8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->lhs->index_end, nullptr);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, IndexedPartSelectComplexBase) {
  auto r = Parse(
      "module t;\n"
      "  logic [63:0] vec;\n"
      "  initial x = vec[(i * 8) +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->index->op, TokenKind::kStar);
}

TEST(OperatorAndExpressionParsing, BitSelectWithExprIndex) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[i + 1];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kBinary);
}

TEST(PrimaryParsing, BitSelectSingleDim) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial x = data[5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, PartSelectInIfCondition) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  initial begin\n"
      "    if (data[3:0] == 4'hF) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  ASSERT_NE(stmt->condition->lhs, nullptr);
  EXPECT_EQ(stmt->condition->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->condition->lhs->index_end, nullptr);
}

TEST(AggregateTypeParsing, PackedIndexedPartSelectPlus) {
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

TEST(PrimaryParsing, SelectBitWithPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[15:8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, PartSelectHasIndexEnd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[15:8];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index, nullptr);
  EXPECT_NE(rhs->index_end, nullptr);
}

TEST(ExpressionParsing, PartSelectConstantRange) {
  auto r = Parse("module m; initial x = data[15:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

TEST(ExpressionParsing, PartSelectIndexedPlus) {
  auto r = Parse("module m; initial x = data[0+:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

TEST(ExpressionParsing, PartSelectIndexedMinus) {
  auto r = Parse("module m; initial x = data[7-:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

TEST(PrimaryParsing, NonrangeSelectBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial data[3] = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, BitSelectAssignedFromFuncCall) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] vec;\n"
      "  initial vec[0] = get_bit();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(OperatorAndExpressionParsing, IndexedPartSelectInForLoop) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [31:0] data;\n"
              "  logic [7:0] bytes [4];\n"
              "  initial begin\n"
              "    for (int i = 0; i < 4; i++)\n"
              "      bytes[i] = data[i*8 +: 8];\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, IndexedPartSelectDownOnLhs) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  initial vec[j -: 4] = 4'b1010;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* lhs = FirstAssignLhs(r);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(lhs->is_part_select_minus);
  EXPECT_FALSE(lhs->is_part_select_plus);
  ASSERT_NE(lhs->index, nullptr);
  ASSERT_NE(lhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, SelectOnFuncReturnValue) {
  auto r = Parse(
      "module t;\n"
      "  initial x = get_data()[7:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kCall);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, SelectOnSystemFuncResult) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = $random[3:0];\n"
              "endmodule\n"));
}

}  // namespace
