#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PatternParsing, PatternConstantExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      5: y = 8'd10;\n"
      "      10: y = 8'd20;\n"
      "      default: y = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternTagged) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(v) matches\n"
      "      tagged Valid .n: x = n;\n"
      "      tagged Invalid: x = 0;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternTaggedWithAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(instr) matches\n"
      "      tagged Add '{.r1, .r2, .rd}: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternTaggedNested) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(instr) matches\n"
      "      tagged Jmp (tagged JmpU .a): pc = a;\n"
      "      default: pc = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternAssignmentWithDotBindings) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(s) matches\n"
      "      '{.a, .b}: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternDotIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .n) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternWildcard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .*) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternGuardExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .n &&& (n > 0)) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches (.n)) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternMemberKeyed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(s) matches\n"
      "      '{first: .a, second: .b}: x = a + b;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, Positional) {
  auto r = Parse(
      "module m;\n"
      "  int a[3];\n"
      "  initial a = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

TEST(AssignmentPatternParsing, StructureKeyed) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; } pt_t;\n"
      "  pt_t p;\n"
      "  initial p = '{x: 1, y: 2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->pattern_keys.size(), 2u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "x");
  EXPECT_EQ(stmt->rhs->pattern_keys[1], "y");
}

TEST(AssignmentPatternParsing, ArrayKeyed) {
  auto r = Parse(
      "module m;\n"
      "  int a[3];\n"
      "  initial a = '{0: 10, 1: 20, 2: 30};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->pattern_keys.size(), 3u);
}

TEST(AssignmentPatternParsing, DefaultKey) {
  auto r = Parse(
      "module m;\n"
      "  int a[4];\n"
      "  initial a = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->pattern_keys.size(), 1u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "default");
}

TEST(AssignmentPatternParsing, SimpleTypeKey) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int i; real r; } both_t;\n"
      "  both_t b;\n"
      "  initial b = '{int: 5, real: 1.5};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->pattern_keys.size(), 2u);
}

TEST(AssignmentPatternParsing, Replication) {
  auto r = Parse(
      "module m;\n"
      "  int a[6];\n"
      "  initial a = '{3{0, 1}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->elements.size(), 1u);
  EXPECT_EQ(stmt->rhs->elements[0]->kind, ExprKind::kReplicate);
}

TEST(AssignmentPatternExpressionParsing, IntegerAtomTypePrefix) {
  auto r = Parse(
      "module m;\n"
      "  int a[3];\n"
      "  initial a = int'{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(AssignmentPatternExpressionParsing, TypeReferencePrefix) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  int a[2];\n"
      "  initial a = type(x)'{4, 5};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(AssignmentPatternExpressionParsing, TypeParameterPrefix) {
  auto r = Parse(
      "module m;\n"
      "  parameter type T = int;\n"
      "  T x[2];\n"
      "  initial x = T'{7, 8};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(AssignmentPatternExpressionParsing, UserTypePrefix) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int i; int j; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = pair_t'{i: 1, j: 2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(AssignmentPatternLvalueParsing, NetLvalueInContinuousAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] x, y;\n"
      "  assign '{x, y} = '{4'h1, 4'h2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleItem* assign_item = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      assign_item = item;
      break;
    }
  }
  ASSERT_NE(assign_item, nullptr);
  ASSERT_NE(assign_item->assign_lhs, nullptr);
  EXPECT_EQ(assign_item->assign_lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(PatternParsing, PatternTaggedMissingMember) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(v) matches\n"
      "      tagged: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(AssignmentPatternParsing, SingleElement) {
  auto r = Parse(
      "module m;\n"
      "  int a[1];\n"
      "  initial a = '{42};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 1u);
}

TEST(AssignmentPatternParsing, NestedPatterns) {
  auto r = Parse(
      "module m;\n"
      "  int a[2][2];\n"
      "  initial a = '{'{1, 2}, '{3, 4}};\n"
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

TEST(AssignmentPatternParsing, UnclosedBrace) {
  auto r = Parse(
      "module m;\n"
      "  int a[2];\n"
      "  initial a = '{1, 2;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssignmentPatternLvalueParsing, VariableLvalueInProceduralAssign) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  initial '{a, b} = '{10, 20};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kAssignmentPattern);
}

// §A.6.7.1 constant_assignment_pattern_expression ::=
// assignment_pattern_expression. The same '{...} assignment pattern must be
// accepted in a constant-expression position — here a localparam initializer —
// not only in the procedural and continuous-assign positions the other tests
// cover. The parser reaches the same ParseAssignmentPattern code, so the
// resulting node is a plain kAssignmentPattern.
TEST(ConstantAssignmentPatternExpressionParsing, PositionalInLocalparam) {
  auto r = Parse(
      "module m;\n"
      "  localparam int LP[3] = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = FindItemByKind(r, ModuleItemKind::kParamDecl);
  ASSERT_NE(param, nullptr);
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(param->init_expr->elements.size(), 3u);
}

// §A.6.7.1: a member-keyed structure pattern is equally valid as a
// constant_assignment_pattern_expression; drive it through a value parameter's
// default (a constant-expression position) built from a real struct typedef.
TEST(ConstantAssignmentPatternExpressionParsing, StructureKeyedInParameter) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; } pt_t;\n"
      "  parameter pt_t P = '{x: 1, y: 2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = FindItemByKind(r, ModuleItemKind::kParamDecl);
  ASSERT_NE(param, nullptr);
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(param->init_expr->pattern_keys.size(), 2u);
  EXPECT_EQ(param->init_expr->pattern_keys[0], "x");
  EXPECT_EQ(param->init_expr->pattern_keys[1], "y");
}

// §A.6.7.1 assignment_pattern ::= '{ constant_expression { expression {, ...} }
// }. The replication count is a constant_expression; exercise the parameter
// form (a §11.2.1 constant other than an integer literal, unlike the
// Replication test above). The count node is the referenced identifier, not a
// literal.
TEST(AssignmentPatternParsing, ReplicationCountFromParameter) {
  auto r = Parse(
      "module m;\n"
      "  parameter N = 3;\n"
      "  int a[6];\n"
      "  initial a = '{N{0, 1}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->elements.size(), 1u);
  auto* rep = stmt->rhs->elements[0];
  EXPECT_EQ(rep->kind, ExprKind::kReplicate);
  ASSERT_NE(rep->repeat_count, nullptr);
  EXPECT_EQ(rep->repeat_count->kind, ExprKind::kIdentifier);
}

// §A.6.7.1 pattern ::= constant_expression. The PatternConstantExpr test covers
// the integer-literal constant form; a named constant (a localparam) is the
// other §11.2.1 constant form and reaches the pattern through the identifier
// branch of primary-expression parsing rather than the literal branch.
// Complements the literal case so both constant-expression parse paths are
// observed.
TEST(PatternParsing, PatternConstantExprParameter) {
  auto r = Parse(
      "module m;\n"
      "  localparam P = 5;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      P: y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.6.7.1 negative: the keyed assignment-pattern form
// '{ structure_pattern_key : expression } requires an expression after the
// colon. Omitting it must be rejected at parse time.
TEST(AssignmentPatternParsing, KeyedMissingValue) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  initial a = '{x:};\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §A.6.7.1 negative: pattern ::= . variable_identifier requires an identifier
// after the dot; a dot with no following identifier must be rejected.
TEST(PatternParsing, PatternDotMissingIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .) x = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
