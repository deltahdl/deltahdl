#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// An empty named parameter expression is permitted: the parentheses are
// required but the expression is optional (the override is left to default).
TEST(ModuleInstanceParameterAssignment, EmptyNamedParameterExpressionParses) {
  auto r = Parse("module m; sub #(.W()) u0(a); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// The parentheses around a named parameter override are mandatory; a bare
// .name with no parentheses is a syntax error.
TEST(ModuleInstanceParameterAssignment, NamedParameterRequiresParentheses) {
  auto r = Parse("module m; sub #(.W) u0(a); endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got ')'", 1, "23.10.2.2"));
}

TEST(ModuleInstanceParameterAssignment, MixedOrderedThenNamedRejected) {
  auto r = Parse("module m; sub #(8, .B(4)) u0(a); endmodule\n");
  // src/parser/parser_inst.cpp:146 files the ordered/named mix under §23.3.2.
  EXPECT_TRUE(ReportedError(
      r.diags, "ordered and named parameter value assignments cannot be mixed",
      1, "23.3.2"));
}

TEST(ModuleInstanceParameterAssignment, DuplicateNamedParameterRejected) {
  auto r = Parse("module m; sub #(.W(8), .W(16)) u0(a); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "duplicate parameter name 'W' in parameter value assignment", 1,
      "23.10.2.2"));
}

}  // namespace
