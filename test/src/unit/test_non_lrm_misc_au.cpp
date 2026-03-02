// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.2 Subroutine calls — method_call_body / built_in_method_call
// =============================================================================
// § method_call_body ::= method_identifier { attribute_instance }
//                        [ ( list_of_arguments ) ]
//                      | built_in_method_call
// § built_in_method_call ::= array_manipulation_call | randomize_call
// =============================================================================
// A.8.2 Subroutine calls — array_manipulation_call
// =============================================================================
// § array_manipulation_call ::= array_method_name { attribute_instance }
//                              [ ( list_of_arguments ) ]
//                              [ with ( expression ) ]
// array_manipulation_call: sum with no args
TEST(ParserA82, ArrayManipCallSum) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.sum(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// array_manipulation_call with 'with' clause
TEST(ParserA82, ArrayManipCallWithClause) {
  auto r = Parse(
      "module m;\n"
      "  int arr[4];\n"
      "  int result[$];\n"
      "  initial begin result = arr.find with (item > 5); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.2 Subroutine calls — array_method_name
// =============================================================================
// § array_method_name ::= method_identifier | unique | and | or | xor
TEST(ParserA82, ArrayMethodNameUnique) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.unique(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, ArrayMethodNameAnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.and(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, ArrayMethodNameOr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.or(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, ArrayMethodNameXor) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.xor(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.2 Subroutine calls — randomize_call
// =============================================================================
// § randomize_call ::= randomize { attribute_instance }
//   [ ( [ variable_identifier_list | null ] ) ]
//   [ with [ ( [ identifier_list ] ) ] constraint_block ]
TEST(ParserA82, RandomizeCallBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, RandomizeCallWithConstraintBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize() with { x < 10; }; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, RandomizeCallWithNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(null); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, RandomizeCallWithVarList) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(x, y); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § std::randomize_call (subroutine_call alternative)
TEST(ParserA82, StdRandomizeCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin std::randomize(x) with { x > 0; }; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.2 Subroutine calls — variable_identifier_list / identifier_list
// =============================================================================
// § variable_identifier_list ::= variable_identifier { , variable_identifier }
// § identifier_list ::= identifier { , identifier }
// Tested implicitly via randomize_call with var list above.
// variable_identifier_list in randomize
TEST(ParserA82, VariableIdentifierList) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(a, b, c); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

}  // namespace
