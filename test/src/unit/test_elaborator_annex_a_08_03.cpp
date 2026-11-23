#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ExpressionElaboration, ConstantExpressionInParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 2 + 3;\n"
      "  logic [P-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConstantTernaryInParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter A = 1;\n"
      "  parameter B = (A > 0) ? 8 : 16;\n"
      "  logic [B-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConstantExpressionInLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter W = 4;\n"
      "  localparam MASK = (1 << W) - 1;\n"
      "  logic [W-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, GenvarExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConditionalExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, x;\n"
      "  assign x = a ? b : 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, InsideExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic hit;\n"
      "  initial hit = x inside {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, IncDecExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    i++;\n"
      "    ++i;\n"
      "    i--;\n"
      "    --i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, PartSelectAndIndexedRangeElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] a, b, c;\n"
      "  assign a = data[15:8];\n"
      "  assign b = data[0+:8];\n"
      "  assign c = data[15-:8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, MintypMaxExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (1:2:3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConstantParamExpressionDollarElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, TaggedUnionExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int v; void i; } u_t;\n"
      "  u_t u;\n"
      "  initial u = tagged v 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ParamExpressionDataTypeOverrideElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub #(parameter type T = int);\n"
      "  T data;\n"
      "endmodule\n"
      "module m;\n"
      "  sub #(.T(logic [7:0])) inst();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ExprOperatorAssignmentElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer x, y;\n"
      "  initial begin\n"
      "    y = 1;\n"
      "    x = (y += 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConstantMintypmaxParameterValueFoldsToTypical) {
  struct Source {
    const char* where;
    const char* src;
    const char* read;
  };
  const Source kSources[] = {
      {"parenthesized localparam in a module body",
       "module m;\n  localparam int P = (1:2:3);\nendmodule\n", "P"},
      {"parameter in a module body",
       "module m;\n  parameter int P = 1:2:3;\nendmodule\n", "P"},
      {"localparam in a module body",
       "module m;\n  localparam int P = 1:2:3;\nendmodule\n", "P"},
      {"members written as constant expressions",
       "module m;\n  localparam int L = 2;\n"
       "  localparam int P = L - 1:L:L + 1;\nendmodule\n",
       "P"},
      {"parameter in a port list",
       "module m #(parameter int P = 1:2:3);\nendmodule\n", "P"},
      {"localparam in a port list",
       "module m #(localparam int P = 1:2:3, int Q = 0);\nendmodule\n", "P"},
      {"parameter in a package",
       "package pk;\n  parameter int P = 1:2:3;\nendpackage\n"
       "module m;\n  localparam int Q = pk::P;\nendmodule\n",
       "Q"},
      {"parameter in the compilation unit",
       "parameter int P = 1:2:3;\nmodule m;\n  localparam int Q = P;\n"
       "endmodule\n",
       "Q"},
      {"localparam in a generate block",
       "module m;\n  if (1) begin : g\n    localparam int P = 1:2:3;\n"
       "  end\nendmodule\n",
       "P"},
  };
  for (const Source& source : kSources) {
    SCOPED_TRACE(source.where);
    ElabFixture f;
    auto* design = ElaborateSrc(source.src, f);
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors);
    const auto* p = FindParam(design, "m", source.read);
    ASSERT_NE(p, nullptr);
    EXPECT_TRUE(p->is_resolved);
    EXPECT_EQ(p->resolved_value, 2);
  }
}

TEST(ExpressionElaboration, ConstantMintypmaxClassParameterValueIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C #(int P = 1:2:3);\n"
      "  parameter int Q = 4:5:6;\n"
      "endclass\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, MintypmaxParameterValueWithAVariableIsReported) {
  struct Source {
    const char* where;
    const char* src;
    const char* message;
    uint32_t line;
    const char* subclause;
  };
  const Source kSources[] = {
      {"variable maximum of a localparam",
       "module m;\n  int v;\n  localparam int P = 1:2:v;\nendmodule\n",
       "localparam 'P' initializer is not a constant expression", 3, "6.20.4"},
      {"variable typical member of a parenthesized parameter",
       "module m;\n  int v;\n  parameter int P = (1:v:3);\nendmodule\n",
       "parameter 'P' value is not a constant expression", 3, "6.20.2"},
      {"variable minimum of a port-list parameter",
       "int v;\nmodule m #(parameter int P = v:2:3);\nendmodule\n",
       "parameter 'P' value is not a constant expression", 2, "6.20.2"},
      {"variable member of a class parameter",
       "int v;\nclass C #(int P = 1:v:3);\nendclass\n",
       "class parameter 'P' value is not a constant expression", 2, "6.20.2"},
  };
  for (const Source& source : kSources) {
    SCOPED_TRACE(source.where);
    ElabFixture f;
    ElaborateSrc(source.src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), source.message, source.line,
                              source.subclause));
  }
}

TEST(ExpressionElaboration, AnAttributeAfterAConstantOperatorLeavesItsValue) {
  struct Folding {
    const char* value;
    int64_t expected;
  };
  const Folding kFoldings[] = {
      {"- (* keep *) 3", -3},           {"7 - (* t *) 2", 5},
      {"7 - (* t *) 2 - (* u *) 1", 4}, {"1 ? (* t *) 5 : 6", 5},
      {"0 ? (* t *) 5 : 6", 6},
  };
  for (const char* keyword : {"parameter", "localparam"}) {
    for (const Folding& folding : kFoldings) {
      ElabFixture f;
      auto* design =
          ElaborateSrc(std::string("module m;\n  ") + keyword +
                           " int P = " + folding.value + ";\nendmodule\n",
                       f);
      ASSERT_NE(design, nullptr) << folding.value;
      EXPECT_FALSE(f.has_errors) << folding.value;
      const auto* p = FindParam(design, "m", "P");
      ASSERT_NE(p, nullptr) << folding.value;
      EXPECT_TRUE(p->is_resolved) << folding.value;
      EXPECT_EQ(p->resolved_value, folding.expected)
          << keyword << " " << folding.value;
    }
  }
}

}  // namespace
