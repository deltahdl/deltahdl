#include <iterator>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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
  EXPECT_EQ(rhs->pattern_keys[0]->text, "a");
  EXPECT_EQ(rhs->pattern_keys[1]->text, "b");
  EXPECT_EQ(rhs->elements.size(), 2u);
}

// §10.9: Syntax 10-5 writes an array key as `array_pattern_key ::=
// constant_expression | assignment_pattern_key`, and a constant expression may
// take as many tokens as it needs. Every other keyed pattern in this file
// writes each key as one token, where the token and the key are the same thing
// and a reader that takes exactly one token per key answers rightly. Here they
// are not the same: taking one token finds `N` where the key is `N-1`, and then
// a minus sign where a colon was expected.
TEST(AssignmentPatternParsing, ArrayPatternKeyIsAConstantExpression) {
  auto r = Parse(
      "module m;\n"
      "  parameter N = 3;\n"
      "  initial begin\n"
      "    x = '{N-1: 10, N: 20};\n"
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
  EXPECT_EQ(rhs->pattern_keys[0]->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->pattern_keys[1]->text, "N");
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
  EXPECT_TRUE(ReportedError(r.diags, "expected '}', got ';'", 3, "10.9"));
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
  // The inner '}' closes the replication under §10.9.1, so the brace the
  // pattern itself is missing is the one §10.9 asks for at the ';'.
  EXPECT_TRUE(ReportedError(r.diags, "expected '}', got ';'", 3, "10.9"));
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

// §10.9 gives the form its own production, `assignment_pattern_expression ::=
// [ assignment_pattern_expression_type ] assignment_pattern`, whose type is one
// of `ps_type_identifier`, `ps_parameter_identifier`, `integer_atom_type` or
// `type_reference`, and the clause puts the whole of it on the left: "When an
// assignment pattern expression is used in a left-hand expression, the
// positional notation shall be required". So `pair_t'{a, b} = 16'hABCD;` is an
// assignment whose target carries a type-name prefix, and the clause's own
// example writes exactly that as a procedural statement.
//
// Between `begin` and `end` it was read instead as a §6.8 `data_declaration`
// opening with the data type `pair_t`, and rejected at the apostrophe with
// "expected identifier, got '{" and "expected ';', got '{", both citing §6.8.
// The wrong answer is not visible in the values. Neither rejection consumes the
// token it names, so the body loop goes on to read the bare `'{a, b} =
// 16'hABCD;` that the abandoned declaration left standing, and §10.9 requires
// each member expression to have "the same number of bits as the corresponding
// element in the data type of the assignment pattern expression", which makes
// the bare pattern slice the right-hand value exactly as the typed one does.
// Reading `a` and `b` back therefore passes either way.
//
// The shape is what discriminates. A block that parsed this source holds one
// statement; a block that misparsed it holds two, the fabricated declaration
// and the recovered assignment behind it, and that recovered assignment has
// lost the prefix, so its target is a bare pattern where §10.9 asks for a cast
// over one.
TEST(AssignmentPatternParsing,
     TypedLhsPatternInsideSequentialBlockIsNotADeclaration) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    pair_t'{a, b} = 16'hABCD;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 1u);
  auto* stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kCast);
  ASSERT_NE(stmt->lhs->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->lhs->kind, ExprKind::kAssignmentPattern);
}

// §10.4.2 gives the nonblocking assignment the same target the blocking one
// takes: "variable_lvalue is a data type that is valid for a procedural
// assignment statement", the words §10.4.1 uses at Syntax 10-2. §10.9's typed
// assignment pattern expression is such a target, so both spellings of the
// operator accept it and both were rejected at the apostrophe with the two §6.8
// reports.
//
// This is written out rather than folded into the case above because the
// question is settled by a list that names the two operators separately, so an
// answer can be given for `=` and withheld from `<=`. Neither operator is what
// the decision actually turns on: the pattern stands between the type name and
// whichever operator follows it, so the token that has to be admitted is the
// `'{`, and admitting it answers for both at once. The same recovery hides the
// same misparse from the values here, so the assertions are again the statement
// count and the shape of the target.
TEST(AssignmentPatternParsing,
     TypedLhsPatternInsideSequentialBlockTakesTheNonblockingOperator) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    pair_t'{a, b} <= 16'hABCD;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 1u);
  auto* stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kCast);
  ASSERT_NE(stmt->lhs->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->lhs->kind, ExprKind::kAssignmentPattern);
}

// §10.9 says nothing about which body an assignment pattern expression may be a
// target in, and a function body is a body like any other, so `pair_t'{a, b} =
// 16'hABCD;` written straight into one is the same assignment as inside a
// `begin`-`end` block. The `begin` is deliberately absent: a function body
// reads its statements from its own loop, and that loop asks the same question
// about a leading known type name that the sequential block's loop asks. With
// no block in the source there is no other loop this statement can be reached
// through, so a source accepted here is one where the question was answered
// where it is asked rather than in the sequential block alone -- which is what
// carries the answer to the parallel block, the task body and the randsequence
// code block, none of which is written out separately.
TEST(AssignmentPatternParsing, TypedLhsPatternInsideFunctionBody) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  logic [7:0] a, b;\n"
      "  function void f();\n"
      "    pair_t'{a, b} = 16'hABCD;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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

// §10.9 closes every assignment pattern with the '}' that Syntax 10-5 writes,
// whichever of the two element forms the pattern used. A pattern left open is
// rejected at the token standing where the '}' belongs, and the report names
// §10.9 rather than the token it wanted.
//
// The rejection is written over the closing brace rather than over the ':' that
// separates a key from its value, because a pattern element is read as an
// expression first and only a ':' behind it makes what was read a key: the
// parser reaches the ':' only once it has seen one, so no source makes that
// call report.
TEST(AssignmentPattern, MalformedPatternNames10_9) {
  auto r = Parse(
      "module m;\n"
      "  int a[2] = '{1, 2;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '}'", 2, "10.9"));
}

}  // namespace
