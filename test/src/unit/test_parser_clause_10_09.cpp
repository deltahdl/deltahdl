#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AssignmentPatternParsing, IntegerAtomTypePrefix) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a = int'{1};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, IntegerAtomTypePrefixedWithKeys) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = int'{31: 1, default: 0};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, PositionalFourElements) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{1, 2, 3, 4};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 4u);
}

TEST(AssignmentPatternParsing, EmptyAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 0u);
}

TEST(AssignmentPatternParsing, ReplicationMultipleElements) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{2{a, b}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, DefaultKeyVerified) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  std::string expected_keys[] = {"default"};
  VerifyPatternKeys(rhs, expected_keys, std::size(expected_keys));
}

TEST(AssignmentPatternParsing, ArrayOfStructsPattern) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  pair_t arr[2];\n"
              "  initial begin\n"
              "    arr[0] = '{1, 2};\n"
              "    arr[1] = '{3, 4};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(AssignmentPatternParsing, AssignmentPatternKeysPopulated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{a: 1, b: 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->pattern_keys.size(), 2u);
  EXPECT_EQ(rhs->pattern_keys[0], "a");
  EXPECT_EQ(rhs->pattern_keys[1], "b");
  EXPECT_EQ(rhs->elements.size(), 2u);
}

TEST(AssignmentPatternParsing, NetLvalueAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign '{a, b} = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, VarLvalueAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    '{a, b} = '{1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, VarLvalueAssignmentPatternWithIndex) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    '{a[0], b[1]} = '{1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, ErrorAssignmentPatternMissingCloseBrace) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{1, 2, 3;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssignmentPatternParsing, ErrorAssignmentPatternMissingApostrophe) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = {1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_NE(rhs->kind, ExprKind::kAssignmentPattern);
}

TEST(AssignmentPatternParsing, ErrorReplicationMissingCloseBrace) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{3{8'd5};\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssignmentPatternParsing, ByteTypePrefix) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  byte b;\n"
              "  initial b = byte'{8'd42};\n"
              "endmodule\n"));
}

TEST(AssignmentPatternParsing, ShortintTypePrefix) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  shortint s;\n"
              "  initial s = shortint'{16'd100};\n"
              "endmodule\n"));
}

TEST(AssignmentPatternParsing, LongintTypePrefix) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  longint l;\n"
              "  initial l = longint'{64'd0};\n"
              "endmodule\n"));
}

TEST(AssignmentPatternParsing, IntegerTypePrefix) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  integer i;\n"
              "  initial i = integer'{42};\n"
              "endmodule\n"));
}

TEST(AssignmentPatternParsing, TimeTypePrefix) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  time t;\n"
              "  initial t = time'{0};\n"
              "endmodule\n"));
}

TEST(AssignmentPatternParsing, TypeReferenceWithMultipleElements) {
  auto r = Parse(
      "module m;\n"
      "  logic [23:0] x;\n"
      "  initial x = type(x)'{8'd1, 8'd2, 8'd3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

TEST(AssignmentPatternParsing, SingleElementReplication) {
  auto r = Parse(
      "module m;\n"
      "  initial x = '{1{8'hFF}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->elements.size(), 1u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kReplicate);
}

TEST(AssignmentPatternParsing, SimpleTypeAsAssignmentPatternKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int x;\n"
              "  initial x = '{int: 5, default: 0};\n"
              "endmodule\n"));
}

TEST(AssignmentPatternParsing, PsTypeIdentifierAsExpressionType) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = pair_t'{8'h12, 8'h34};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(AssignmentPatternParsing, ConstantAssignmentPatternExpressionInParameter) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter int p = int'{42};\n"
              "endmodule\n"));
}

// §10.9's syntax gives an assignment pattern a positional form and a keyed one
// that can open with the very same token:
//
//   assignment_pattern ::= ' { expression { , expression } }
//                        | ' { array_pattern_key : expression { ... } }
//   array_pattern_key  ::= constant_expression | assignment_pattern_key
//
// A string literal is a constant expression, so it can be either an item or a
// key, and only the colon after it settles which. Written without one it is the
// first `expression` of the positional form, and §10.10.3 writes exactly that:
//
//   SQ = '{"element 0", "element 1"};   // assignment pattern, two strings
//
// Both positions are checked, and separately, because the two are reached by
// different routes. Only the first item is the one the colon question hangs
// over; every later item is read as an expression with nothing to decide. A
// first item that came out as some other kind of node while the second was a
// string literal is the signature of the lookahead being resolved by rebuilding
// the token rather than by re-reading it.
TEST(AssignmentPatternParsing, StringLiteralFirstItemIsAnExpressionNotAKey) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{\"element 0\", \"element 1\"};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_TRUE(rhs->pattern_keys.empty());
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kStringLiteral);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kStringLiteral);
}

// The other side of the same decision, so that reading the leading literal as
// an item cannot be done by forgetting that it may be a key. With a colon after
// it the literal is an `array_pattern_key` and the value behind the colon is
// the element, which is how an associative array indexed by string is written.
TEST(AssignmentPatternParsing, StringLiteralBeforeAColonIsAKey) {
  auto r = Parse(
      "module m;\n"
      "  initial x = '{\"Peter\": 20, \"Paul\": 22};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  std::string expected_keys[] = {"\"Peter\"", "\"Paul\""};
  VerifyPatternKeys(rhs, expected_keys, std::size(expected_keys));
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kIntegerLiteral);
}

}  // namespace
