#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ModuleInstanceParameterAssignment, EmptyNamedParameterExpressionParses) {
  auto r = Parse("module m; sub #(.W()) u0(a); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleInstanceParameterAssignment, NamedParameterRequiresParentheses) {
  auto r = Parse("module m; sub #(.W) u0(a); endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got ')'", 1, "23.10.2.2"));
}

TEST(ModuleInstanceParameterAssignment, MixedOrderedThenNamedRejected) {
  auto r = Parse("module m; sub #(8, .B(4)) u0(a); endmodule\n");
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
