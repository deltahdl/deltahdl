#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

static ModuleItem* FirstContAssign(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

namespace {

TEST(LvalueParsing, NetLvalueSimpleIdent) {
  auto r = Parse("module m; wire a, b; assign a = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ca->assign_lhs->text, "a");
}

TEST(LvalueParsing, NetLvalueConstBitSelect) {
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

TEST(LvalueParsing, NetLvalueConstPartSelect) {
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

TEST(LvalueParsing, NetLvalueConcatenation) {
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

TEST(LvalueParsing, NetLvalueNestedConcatenation) {
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

TEST(LvalueParsing, NetLvalueConcatWithSelects) {
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

TEST(LvalueParsing, VarLvalueSimpleIdent) {
  auto r = Parse("module m; logic x; initial x = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "x");
}

TEST(LvalueParsing, VarLvalueBitSelect) {
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

TEST(LvalueParsing, VarLvaluePartSelect) {
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

TEST(LvalueParsing, VarLvalueIndexedPartSelectPlus) {
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

TEST(LvalueParsing, VarLvalueIndexedPartSelectMinus) {
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

TEST(LvalueParsing, VarLvalueMemberAccess) {
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

TEST(LvalueParsing, VarLvalueConcatenation) {
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

TEST(LvalueParsing, VarLvalueNestedConcatenation) {
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

TEST(LvalueParsing, NonrangeVarLvalueSimple) {
  auto r = Parse("module m; int x; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "x");
}

TEST(LvalueParsing, VarLvalueStreamingConcatRightShift) {
  auto r = Parse(
      "module m; logic [31:0] a, b;\n"
      "  initial {>> {a, b}} = 64'hDEADBEEF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->lhs->op, TokenKind::kGtGt);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
}

TEST(LvalueParsing, VarLvalueStreamingConcatLeftShift) {
  auto r = Parse(
      "module m; logic [7:0] a, b;\n"
      "  initial {<< byte {a, b}} = 16'hABCD;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->lhs->op, TokenKind::kLtLt);
  ASSERT_NE(stmt->lhs->lhs, nullptr);
}

TEST(LvalueParsing, VarLvalueStreamingConcatWithSliceSize) {
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

TEST(LvalueParsing, VarLvalueStreamingConcatNonblocking) {
  auto r = Parse(
      "module m; logic [7:0] x;\n"
      "  initial {>> {x}} <= 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
}

TEST(LvalueParsing, VarLvalueStreamingConcatFromStreamingRhs) {
  auto r = Parse(
      "module m; logic [7:0] a, b, c, d;\n"
      "  initial {>> {a, b}} = {>> {c, d}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
}

TEST(LvalueParsing, VarLvalueHierarchicalMember) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] x; } inner_t;\n"
      "  typedef struct packed { inner_t sub; } outer_t;\n"
      "  outer_t o;\n"
      "  initial o.sub.x = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(LvalueParsing, VarLvalueArrayElement) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  integer i;\n"
      "  initial arr[i] = 8'hAB;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(LvalueParsing, NetLvalueMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
      "  wire s_t s;\n"
      "  assign s.a = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kMemberAccess);
}

TEST(LvalueParsing, VarLvalueMemberAccessWithBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p.hi[3] = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(LvalueParsing, VarLvalueConcatWithMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } s_t;\n"
      "  s_t s;\n"
      "  logic [3:0] x;\n"
      "  initial {s.a, x} = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements[0]->kind, ExprKind::kMemberAccess);
}

TEST(LvalueParsing, NetLvalueAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] x, y;\n"
      "  assign '{x, y} = '{4'h1, 4'h2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(ca->assign_lhs->elements.size(), 2u);
}

TEST(LvalueParsing, NetLvalueAssignmentPatternTypedPrefix) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  wire [3:0] x, y;\n"
      "  assign pair_t'{x, y} = 8'hAB;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kCast);
  ASSERT_NE(ca->assign_lhs->lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(LvalueParsing, VarLvalueAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  initial '{a, b} = '{10, 20};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
}

TEST(LvalueParsing, VarLvalueAssignmentPatternTypedPrefix) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  logic [3:0] a, b;\n"
      "  initial pair_t'{a, b} = 8'hCD;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kCast);
  ASSERT_NE(stmt->lhs->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(LvalueParsing, VarLvalueWithImplicitClassHandle) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  function void set(int v);\n"
      "    this.x = v;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LvalueParsing, VarLvalueWithSuperHandle) {
  // variable_lvalue's optional prefix is `implicit_class_handle .`, and
  // implicit_class_handle admits `super` as well as `this`. Assigning through
  // `super.` exercises the distinct super branch of the lvalue parse.
  auto r = Parse(
      "class B;\n"
      "  int x;\n"
      "endclass\n"
      "class D extends B;\n"
      "  function void set(int v);\n"
      "    super.x = v;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LvalueParsing, VarLvalueWithThisSuperHandle) {
  // implicit_class_handle also admits the `this.super` form; variable_lvalue
  // may carry it as its optional prefix. Assigning through `this.super.`
  // exercises that third handle alternative (distinct from bare `this` and bare
  // `super`).
  auto r = Parse(
      "class B;\n"
      "  int x;\n"
      "endclass\n"
      "class D extends B;\n"
      "  function void set(int v);\n"
      "    this.super.x = v;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LvalueParsing, VarLvalueWithPackageScope) {
  auto r = Parse(
      "class C;\n"
      "  static int count;\n"
      "endclass\n"
      "module m;\n"
      "  initial C::count = 5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

// A.6.2 (printed page 1198) writes the target of a blocking, a nonblocking and
// an operator assignment as a variable_lvalue, which A.8.5 (printed page 1212)
// gives four forms: a name under selects, a concatenation or an assignment
// pattern of variable_lvalues (typed or not), and a streaming concatenation.
// None is written in parentheses, whole or as an element, and a literal or a
// cast of a name is none of them.
TEST(LvalueParsing, ProceduralTargetOfNoVariableLvalueFormIsError) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic a; logic b; } pair_t;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    (a) = b;\n"
      "    (a) <= b;\n"
      "    (a) += b;\n"
      "    1'b0 = b;\n"
      "    {a, (b)} = 2'b00;\n"
      "    pair_t'{a, (b)} = 2'b00;\n"
      "    a = b;\n"
      "    {a, b} = 2'b00;\n"
      "    pair_t'{a, b} = 2'b00;\n"
      "    '{a, b} = 2'b00;\n"
      "    {>>{a, b}} = 2'b00;\n"
      "  end\n"
      "  initial int'(a) = b;\n"
      "endmodule\n");
  for (uint32_t line : {5u, 6u, 7u, 8u, 9u, 10u, 17u}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "this target is neither a variable_lvalue nor a net_lvalue",
        line, "A.8.5"));
  }
  EXPECT_EQ(r.diags.size(), 7u);
}

// A.6.2 (printed page 1198) writes the target of a procedural assign and a
// deassign as a variable_lvalue, and that of a force and a release as a
// variable_lvalue or a net_lvalue; A.8.5 (printed page 1212) writes neither in
// parentheses or as an operation.
TEST(LvalueParsing, ProceduralContinuousTargetOfNoLvalueFormIsError) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    assign (a) = b;\n"
      "    deassign (a);\n"
      "    force (w) = b;\n"
      "    release (w);\n"
      "    force a + b = 1'b0;\n"
      "    assign a = b;\n"
      "    force w = b;\n"
      "    release {a, w};\n"
      "    deassign a;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {5u, 6u, 7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "this target is neither a variable_lvalue nor a net_lvalue",
        line, "A.8.5"));
  }
  EXPECT_EQ(r.diags.size(), 5u);
}

// A.8.5 (printed page 1212) roots variable_lvalue's name form at a
// hierarchical_variable_identifier, so a select of a call's result or a member
// of a name written in parentheses is no target of a blocking or nonblocking
// assignment. A select of a concatenation is no name form either, but §11.4.12
// bars it by name and the elaborator reports it under that subclause, as it
// reports a replication under §11.4.12.1, so the parser leaves it be. A
// parenthesized target assigned a `new` is reported once, as no
// variable_lvalue, and not again as the aggregate A.6.2 refuses a `new` to.
TEST(LvalueParsing, ProceduralTargetRootedAtNoNameIsError) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic a; logic b; } pair_t;\n"
      "  class C; endclass\n"
      "  logic [3:0] a, b;\n"
      "  pair_t s;\n"
      "  C h;\n"
      "  function automatic logic [7:0] f(); return 0; endfunction\n"
      "  initial begin\n"
      "    {a, b}[0] = 1'b1;\n"
      "    f()[1] <= 1'b0;\n"
      "    (s).a = 1'b0;\n"
      "    (h) = new;\n"
      "    s.a = 1'b0;\n"
      "    a[1] <= 1'b0;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {10u, 11u, 12u}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "this target is neither a variable_lvalue nor a net_lvalue",
        line, "A.8.5"));
  }
  EXPECT_EQ(r.diags.size(), 3u);
}

// A.8.3 writes an increment's operand, and A.6.2 the target of an assignment
// within an expression, as a variable_lvalue, whose name form A.8.5 (printed
// page 1212) roots at a hierarchical_variable_identifier: a select of a call's
// result or a member of a name written in parentheses is neither.
TEST(LvalueParsing, ExpressionTargetRootedAtNoNameIsError) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic a; logic b; } pair_t;\n"
      "  logic [3:0] a, x;\n"
      "  pair_t s;\n"
      "  function automatic logic [7:0] f(); return 0; endfunction\n"
      "  initial begin\n"
      "    ++(s).a;\n"
      "    f()[1]++;\n"
      "    x = ((s).a = 1'b1);\n"
      "    x = (f()[1] = 1'b0);\n"
      "    a[0]++;\n"
      "    x = (a[0] = 1'b1);\n"
      "  end\n"
      "endmodule\n");
  constexpr std::string_view kIncDec =
      "an increment or decrement's operand is a variable_lvalue; this one is "
      "not";
  constexpr std::string_view kParenAssign =
      "an assignment within an expression assigns a variable_lvalue; this "
      "target is none";
  EXPECT_TRUE(ReportedError(r.diags, kIncDec, 7, "A.8.3"));
  EXPECT_TRUE(ReportedError(r.diags, kIncDec, 8, "A.8.3"));
  EXPECT_TRUE(ReportedError(r.diags, kParenAssign, 9, "A.6.2"));
  EXPECT_TRUE(ReportedError(r.diags, kParenAssign, 10, "A.6.2"));
  EXPECT_EQ(r.diags.size(), 4u);
}

}  // namespace
