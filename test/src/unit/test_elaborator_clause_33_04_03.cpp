#include "fixture_elaborator.h"

namespace {

// Config-elaborates `src` through its first configuration and returns the cell
// bound to the first child instance of the design's top module, so that
// configuration-applied parameter values can be inspected (§33.4.3).
RtlirModule* ConfigElabFirstChild(ElabFixture& f, const std::string& src) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  f.has_errors = f.diag.HasErrors();
  if (!design || design->top_modules.empty()) return nullptr;
  auto* top = design->top_modules[0];
  if (top->children.empty()) return nullptr;
  return top->children[0].resolved;
}

int64_t ResolvedParam(const RtlirModule* m, std::string_view name) {
  for (const auto& p : m->params) {
    if (p.name == name) return p.resolved_value;
  }
  return -1;
}

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

// A real literal is as much a literal value as an integer or string, so a
// config localparam set directly to one is accepted (§33.4.3).
TEST(ConfigLocalparamLiteral, RealLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam R = 1.5;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

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

// An override with empty parentheses requests a reset to the module default
// and is a legal override; the parameter-override validator must accept it
// rather than treating the absent expression as malformed (§33.4.3).
TEST(ConfigParamOverride, EmptyParamOverrideAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W());\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// An empty override list requests a reset of every parameter to its module
// default and is likewise a legal use clause (§33.4.3).
TEST(ConfigParamOverride, EmptyParamListAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #();\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// The literal-or-config-localparam restriction on index expressions applies to
// every bound of a part-select, not only the first; an unknown identifier in
// the upper/lower bound of a range select is rejected (§33.4.3).
TEST(ConfigParamOverride, RangeSelectBoundNonLiteralRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[2:i]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// The prohibition on calling a user-defined function reaches a call buried
// inside a larger override expression, not only a call standing alone
// (§33.4.3).
TEST(ConfigParamOverride, NestedUserFunctionCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(1 + my_func(2)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// A configuration override applies the named value to the bound instance's
// parameter (§33.4.3).
TEST(ConfigParamApply, OverrideSetsInstanceParameter) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config c; design top; instance top.a1 use #(.W(32)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 32);
}

// An override with empty parentheses returns just that parameter to its module
// default, discarding the value the instantiation supplied (§33.4.3).
TEST(ConfigParamApply, EmptyOverrideResetsParameterToDefault) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; adder #(.W(16)) a1 (); endmodule\n"
      "config c; design top; instance top.a1 use #(.W()); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 8);
}

// An empty override list returns every parameter to its module default,
// discarding all values the instantiation supplied (§33.4.3).
TEST(ConfigParamApply, EmptyListResetsAllParametersToDefault) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8, parameter D = 4) (); endmodule\n"
      "module top; adder #(.W(16), .D(2)) a1 (); endmodule\n"
      "config c; design top; instance top.a1 use #(); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 8);
  EXPECT_EQ(ResolvedParam(a1, "D"), 4);
}

// A configuration override of a parameter takes precedence over a defparam
// targeting the same parameter at the same level of hierarchy (§33.4.3).
TEST(ConfigParamApply, OverrideTakesPrecedenceOverDefparam) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; adder a1(); defparam a1.W = 16; endmodule\n"
      "config c; design top; instance top.a1 use #(.W(32)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 32);
}

}  // namespace
