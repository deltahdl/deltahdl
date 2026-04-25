#include "fixture_elaborator.h"

namespace {

// §33.4.3 item 1: a localparam in a configuration shall only be set to
// a literal value.  A non-literal initialiser (a binary expression, a
// reference to another identifier, etc.) is rejected.
TEST(ConfigLocalparamLiteral, NonLiteralLocalparamRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = 1 + 2;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, IdentifierLocalparamRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = a;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// Positive control: an integer literal is allowed.
TEST(ConfigLocalparamLiteral, IntegerLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = 8;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// Positive control: a string literal is allowed.
TEST(ConfigLocalparamLiteral, StringLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam S = \"name\";\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// §33.4.3 item 3: when a hierarchical identifier is used in a
// parameter override, it shall be the only term in the expression.
// `top.WIDTH + 7` is the LRM's textbook example of an invalid form.
TEST(ConfigParamOverride, HierIdentInExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// Positive control: a bare hierarchical identifier as the entire
// override expression is the form §33.4.3 explicitly endorses
// (Example 3: `instance top.a1 use #(.W(top.WIDTH));`).
TEST(ConfigParamOverride, HierIdentAloneAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// Positive control: a non-hierarchical identifier embedded in an
// expression resolves in the instance's parent scope and is fine —
// item 3's restriction targets hierarchical references specifically.
TEST(ConfigParamOverride, NonHierIdentInExpressionAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// §33.4.3 item 2: an identifier appearing inside a select index of a
// hierarchical reference must name a localparam of the configuration.
TEST(ConfigParamOverride, IndexUsingUnknownIdentifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[i]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// Positive control: an integer-literal index is always permitted.
TEST(ConfigParamOverride, IndexUsingLiteralAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[2]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// Positive control: an index identifier that resolves to a localparam
// of the same configuration is accepted.
TEST(ConfigParamOverride, IndexUsingConfigLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam IDX = 0;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[IDX]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// §33.4.3 item 5: a hierarchical reference inside a parameter
// override may not traverse an array-of-instances scope.
TEST(ConfigParamOverride, HierRefThroughArrayOfInstancesRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.arr[0].WIDTH));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §33.4.3 item 6: a parameter override may not call a user-defined
// constant function.
TEST(ConfigParamOverride, UserFunctionCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(my_func(8)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// Positive control for item 6: built-in (system) constant functions
// are explicitly permitted.
TEST(ConfigParamOverride, SystemFunctionCallAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W($clog2(8)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
