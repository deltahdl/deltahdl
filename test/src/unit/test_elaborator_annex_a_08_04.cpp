#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PrimaryElaboration, IntegerLiteralElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  assign x = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, ConstantPrimaryParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 8;\n"
      "  logic [P-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, HierarchicalIdentifierSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  assign x = data[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, ConcatenationWithRangeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic [3:0] x;\n"
      "  initial x = {a, b}[3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, PackageScopedEnumIdentifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef enum { COLOR_RED, COLOR_GREEN, COLOR_BLUE } color_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  int x;\n"
      "  initial x = COLOR_GREEN;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, NullPrimaryElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C; endclass\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = null;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A.10 footnote 50 makes a constant let expression's body constant, with its
// formals counted as constants there. A let whose body reads a variable is no
// constant expression even given a constant argument, nor is a let given a
// variable as its argument; a let over its formal and a parameter is one
// (#8084).
TEST(PrimaryElaboration, ALetCallIsConstantOnlyWhereItsBodyIs) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int K = 3;\n"
      "  int v;\n"
      "  let g(a) = a + v;\n"
      "  let h(a) = a + K;\n"
      "  localparam int P = g(1);\n"
      "  localparam int Q = h(v);\n"
      "  localparam int R = h(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'P' initializer is not a constant expression", 6, "6.20.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'Q' initializer is not a constant expression", 7, "6.20.4"));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'R' initializer is not a constant expression", 8, "6.20.4"));
}

// A.8.4 counts a constant let expression among the constant primaries, so a
// let call folds at elaboration wherever a constant expression stands. Each
// formal takes its argument by position or by name, or its default where the
// argument is left out, and the call's value is the body's (#8085).
TEST(PrimaryElaboration, AConstantLetExpressionFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int K = 3;\n"
      "  let w(n = 4) = n * 2;\n"
      "  let s(a = 1, b = 2) = a + b * 10 + K;\n"
      "  localparam int P = w(5);\n"
      "  localparam int D = w();\n"
      "  localparam int S1 = s(3, 4);\n"
      "  localparam int S2 = s(, 5);\n"
      "  localparam int S3 = s(.b(6));\n"
      "  logic [w(4)-1:0] v;\n"
      "  logic [P-1:0] u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirModule* mod = design->top_modules[0];
  auto param = [mod](std::string_view name) -> int64_t {
    for (const auto& p : mod->params) {
      if (p.name == name) return p.is_resolved ? p.resolved_value : -1;
    }
    return -1;
  };
  EXPECT_EQ(param("P"), 10);
  EXPECT_EQ(param("D"), 8);
  EXPECT_EQ(param("S1"), 46);
  EXPECT_EQ(param("S2"), 54);
  EXPECT_EQ(param("S3"), 64);
  auto width = [mod](std::string_view name) -> uint32_t {
    for (const auto& var : mod->variables) {
      if (var.name == name) return var.width;
    }
    return 0;
  };
  EXPECT_EQ(width("v"), 8U);
  EXPECT_EQ(width("u"), 10U);
}

// A let is its declaring module's, read only while that module is elaborated,
// so a call in a package's or the compilation unit's localparam names that
// scope's function and never a module's let of the same name: the unit's is
// still a constant expression, and the package's never takes the let's value
// (#8085).
TEST(PrimaryElaboration, ALetStandsForNoCallOutsideItsModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  function automatic int f(int x); return x + 1; endfunction\n"
      "  localparam int P = f(1);\n"
      "endpackage\n"
      "function automatic int g(int x); return x + 2; endfunction\n"
      "localparam int Q = g(1);\n"
      "module m;\n"
      "  let f(x) = x * 100;\n"
      "  let g(x) = x * 100;\n"
      "  localparam int R = p::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'Q' initializer is not a constant expression", 6, "6.20.4"));
  ASSERT_FALSE(design->top_modules.empty());
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "R" && param.is_resolved) {
      EXPECT_NE(param.resolved_value, 100);
    }
  }
}

}  // namespace
