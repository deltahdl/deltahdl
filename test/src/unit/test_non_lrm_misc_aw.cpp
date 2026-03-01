// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

static ModuleItem* FirstContAssign(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// A.8.4 Primaries — time_literal and time_unit
// =============================================================================
// § time_literal — unsigned_number time_unit (ns)
TEST(ParserA84, TimeLiteralNs) {
  auto r = Parse("module m; initial #5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (us)
TEST(ParserA84, TimeLiteralUs) {
  auto r = Parse("module m; initial #1us; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (ms)
TEST(ParserA84, TimeLiteralMs) {
  auto r = Parse("module m; initial #2ms; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (s)
TEST(ParserA84, TimeLiteralS) {
  auto r = Parse("module m; initial #1s; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (ps)
TEST(ParserA84, TimeLiteralPs) {
  auto r = Parse("module m; initial #100ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (fs)
TEST(ParserA84, TimeLiteralFs) {
  auto r = Parse("module m; initial #50fs; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — fixed_point_number time_unit
TEST(ParserA84, TimeLiteralFixedPoint) {
  auto r = Parse("module m; initial #1.5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — implicit_class_handle
// =============================================================================
// § implicit_class_handle — this
TEST(ParserA84, ImplicitClassHandleThis) {
  auto r = Parse("module m; initial x = this; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § implicit_class_handle — super
TEST(ParserA84, ImplicitClassHandleSuper) {
  auto r = Parse("module m; initial x = super; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § implicit_class_handle — this with member access
TEST(ParserA84, ImplicitClassHandleThisMember) {
  auto r = Parse("module m; initial x = this.field; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — bit_select
// =============================================================================
// § bit_select — single dimension
TEST(ParserA84, BitSelectSingleDim) {
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

// § bit_select — multi-dimensional
TEST(ParserA84, BitSelectMultiDim) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [7:0] x;\n"
      "  initial x = mem[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

// =============================================================================
// A.8.4 Primaries — select
// =============================================================================
// § select — bit_select with part_select_range
TEST(ParserA84, SelectBitWithPartSelect) {
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

// § select — member_identifier bit_select
TEST(ParserA84, SelectMemberBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic x;\n"
      "  initial x = p.a[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — nonrange_select
// =============================================================================
// § nonrange_select — simple bit_select
TEST(ParserA84, NonrangeSelectBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial data[3] = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — constant_bit_select and constant_select
// =============================================================================
// § constant_bit_select — in packed dimension
TEST(ParserA84, ConstantBitSelectPackedDim) {
  auto r = Parse("module m; logic [7:0] data; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § constant_select — in parameter expression
TEST(ParserA84, ConstantSelectParameterExpr) {
  auto r = Parse(
      "module m;\n"
      "  parameter int A [4] = '{1, 2, 3, 4};\n"
      "  parameter int B = A[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — cast and constant_cast
// =============================================================================
// § cast — type cast in expression
TEST(ParserA84, CastInExpression) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int b;\n"
      "  initial b = int'(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

// § cast — signed cast
TEST(ParserA84, CastSigned) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = signed'(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

// § constant_cast — in parameter
TEST(ParserA84, ConstantCastInParam) {
  auto r = Parse("module m; parameter int P = int'(3.0); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kCast);
}

// =============================================================================
// A.8.4 Primaries — constant_let_expression
// =============================================================================
// § constant_let_expression — let declaration usage
TEST(ParserA84, ConstantLetExpression) {
  auto r = Parse(
      "module m;\n"
      "  let my_let(a) = a + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — system calls as primary
// =============================================================================
// § primary — system function call
TEST(ParserA84, PrimarySystemCall) {
  auto r = Parse("module m; initial x = $clog2(16); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
}

// § primary — type_reference
TEST(ParserA84, PrimaryTypeRef) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    automatic int w;\n"
      "    w = $bits(x);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — escaped identifier as primary
// =============================================================================
// § primary — escaped identifier
TEST(ParserA84, PrimaryEscapedIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  logic \\my-signal ;\n"
      "  initial \\my-signal = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.5 Expression left-side values — net_lvalue
// =============================================================================
// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (simple net)
TEST(ParserA85, NetLvalueSimpleIdent) {
  auto r = Parse("module m; wire a, b; assign a = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ca->assign_lhs->text, "a");
}

// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (bit select)
TEST(ParserA85, NetLvalueConstBitSelect) {
  auto r =
      Parse("module m; wire [7:0] a; wire b; assign a[3] = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_lhs->base, nullptr);
  EXPECT_EQ(ca->assign_lhs->base->text, "a");
}

// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (part
// select)
TEST(ParserA85, NetLvalueConstPartSelect) {
  auto r = Parse(
      "module m; wire [7:0] a; wire [3:0] b; assign a[7:4] = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_lhs->index_end, nullptr);
}

// § net_lvalue — { net_lvalue { , net_lvalue } } (concatenation)
TEST(ParserA85, NetLvalueConcatenation) {
  auto r = Parse(
      "module m; wire [7:0] a; wire [3:0] b, c; assign {b, c} = a; "
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements.size(), 2u);
}

// § net_lvalue — nested concatenation
TEST(ParserA85, NetLvalueNestedConcatenation) {
  auto r = Parse(
      "module m; wire a, b, c, d;\n"
      "  assign {{a, b}, {c, d}} = 4'hF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements.size(), 2u);
  EXPECT_EQ(ca->assign_lhs->elements[0]->kind, ExprKind::kConcatenation);
}

// § net_lvalue — concatenation with selects
TEST(ParserA85, NetLvalueConcatWithSelects) {
  auto r = Parse(
      "module m; wire [7:0] a; wire [3:0] b;\n"
      "  assign {a[7:4], b} = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements[0]->kind, ExprKind::kSelect);
}

// =============================================================================
// A.8.5 Expression left-side values — variable_lvalue
// =============================================================================
// § variable_lvalue — hierarchical_variable_identifier (simple variable)
TEST(ParserA85, VarLvalueSimpleIdent) {
  auto r = Parse("module m; logic x; initial x = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "x");
}

// § variable_lvalue — hierarchical_variable_identifier select (bit select)
TEST(ParserA85, VarLvalueBitSelect) {
  auto r = Parse("module m; logic [7:0] x; initial x[3] = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->lhs->base, nullptr);
  EXPECT_EQ(stmt->lhs->base->text, "x");
  ASSERT_NE(stmt->lhs->index, nullptr);
  EXPECT_EQ(stmt->lhs->index_end, nullptr);
}

// § variable_lvalue — hierarchical_variable_identifier select (part select)
TEST(ParserA85, VarLvaluePartSelect) {
  auto r = Parse("module m; logic [7:0] x; initial x[7:4] = 4'hF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->lhs->index, nullptr);
  ASSERT_NE(stmt->lhs->index_end, nullptr);
}

// § variable_lvalue — hierarchical_variable_identifier select (indexed part
// select +)
TEST(ParserA85, VarLvalueIndexedPartSelectPlus) {
  auto r =
      Parse("module m; logic [15:0] x; initial x[4+:4] = 4'hF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->lhs->is_part_select_plus);
}

// § variable_lvalue — hierarchical_variable_identifier select (indexed part
// select -)
TEST(ParserA85, VarLvalueIndexedPartSelectMinus) {
  auto r =
      Parse("module m; logic [15:0] x; initial x[7-:4] = 4'hF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->lhs->is_part_select_minus);
}

// § variable_lvalue — hierarchical_variable_identifier select (member access)
TEST(ParserA85, VarLvalueMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p.hi = 8'hAB;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

// § variable_lvalue — { variable_lvalue { , variable_lvalue } }
// (concatenation)
TEST(ParserA85, VarLvalueConcatenation) {
  auto r = Parse(
      "module m; logic [3:0] a, b; logic [7:0] c;\n"
      "  initial {a, b} = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
}

// § variable_lvalue — nested concatenation
TEST(ParserA85, VarLvalueNestedConcatenation) {
  auto r = Parse(
      "module m; logic a, b, c, d;\n"
      "  initial {{a, b}, {c, d}} = 4'hF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements[0]->kind, ExprKind::kConcatenation);
}

// § variable_lvalue — streaming_concatenation
TEST(ParserA85, VarLvalueStreamingConcat) {
  auto r = Parse(
      "module m; logic [31:0] a, b;\n"
      "  initial {>> {a}} = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
}

// § variable_lvalue — streaming_concatenation with slice_size
TEST(ParserA85, VarLvalueStreamingConcatSliceSize) {
  auto r = Parse(
      "module m; logic [31:0] a, b;\n"
      "  initial {>> 8 {a}} = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
}

// § variable_lvalue — nonblocking assignment LHS
TEST(ParserA85, VarLvalueNonblocking) {
  auto r = Parse("module m; logic x; initial x <= 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
}

// § variable_lvalue — nonblocking assignment with concatenation LHS
TEST(ParserA85, VarLvalueNonblockingConcat) {
  auto r = Parse(
      "module m; logic [3:0] a, b;\n"
      "  initial {a, b} <= 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

// § variable_lvalue — compound assignment +=
TEST(ParserA85, VarLvalueCompoundAdd) {
  auto r = Parse("module m; int x; initial x += 5; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
}

// § variable_lvalue — compound assignment with bit select LHS
TEST(ParserA85, VarLvalueCompoundBitSelect) {
  auto r = Parse("module m; logic [7:0] x; initial x[3] |= 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

// § variable_lvalue — pre-increment (++ as lvalue modifier)
TEST(ParserA85, VarLvaluePreIncrement) {
  auto r = Parse("module m; int x; initial ++x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — post-increment
TEST(ParserA85, VarLvaluePostIncrement) {
  auto r = Parse("module m; int x; initial x++; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — pre-decrement
TEST(ParserA85, VarLvaluePreDecrement) {
  auto r = Parse("module m; int x; initial --x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — post-decrement
TEST(ParserA85, VarLvaluePostDecrement) {
  auto r = Parse("module m; int x; initial x--; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — multi-dimensional array element select
TEST(ParserA85, VarLvalueMultiDimSelect) {
  auto r = Parse(
      "module m; logic [7:0] mem [0:3][0:3];\n"
      "  initial mem[1][2] = 8'hAB;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

// § variable_lvalue — force statement LHS
TEST(ParserA85, VarLvalueForce) {
  auto r = Parse("module m; logic x; initial force x = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — release statement LHS
TEST(ParserA85, VarLvalueRelease) {
  auto r = Parse(
      "module m; logic x;\n"
      "  initial begin force x = 1; release x; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.5 Expression left-side values — nonrange_variable_lvalue
// =============================================================================
// § nonrange_variable_lvalue — simple identifier (no range)
TEST(ParserA85, NonrangeVarLvalueSimple) {
  auto r = Parse("module m; int x; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "x");
}

// § nonrange_variable_lvalue — member access (no range)
TEST(ParserA85, NonrangeVarLvalueMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
      "  s_t s;\n"
      "  initial s.a = 8'h12;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

// =============================================================================
// A.8.6 Operators — unary_operator
// =============================================================================
// § unary_operator ::= +
TEST(ParserA86, UnaryPlus) {
  auto r = Parse("module m; initial x = +a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

// § unary_operator ::= -
TEST(ParserA86, UnaryMinus) {
  auto r = Parse("module m; initial x = -a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

// § unary_operator ::= !
TEST(ParserA86, UnaryLogicalNot) {
  auto r = Parse("module m; initial x = !a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kBang);
}

// § unary_operator ::= ~
TEST(ParserA86, UnaryBitwiseNot) {
  auto r = Parse("module m; initial x = ~a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

// § unary_operator ::= ~&
TEST(ParserA86, UnaryReductionNand) {
  auto r = Parse("module m; initial x = ~&a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeAmp);
}

// § unary_operator ::= ~|
TEST(ParserA86, UnaryReductionNor) {
  auto r = Parse("module m; initial x = ~|a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildePipe);
}

// § unary_operator ::= ~^
TEST(ParserA86, UnaryReductionXnor) {
  auto r = Parse("module m; initial x = ~^a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

// § unary_operator ::= ^~
TEST(ParserA86, UnaryReductionXnorAlt) {
  auto r = Parse("module m; initial x = ^~a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

// =============================================================================
// A.8.6 Operators — binary_operator (arithmetic)
// =============================================================================
// § binary_operator ::= +
TEST(ParserA86, BinaryAdd) {
  auto r = Parse("module m; initial x = a + b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

// § binary_operator ::= -
TEST(ParserA86, BinarySub) {
  auto r = Parse("module m; initial x = a - b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

// § binary_operator ::= *
TEST(ParserA86, BinaryMul) {
  auto r = Parse("module m; initial x = a * b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

}  // namespace
