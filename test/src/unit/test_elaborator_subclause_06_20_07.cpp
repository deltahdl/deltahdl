#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <format>
#include <initializer_list>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/net_data_type.h"
#include "elaborator/simple_bit_vector.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(DollarConstantElaboration, DollarBodyParameterSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DollarConstantElaboration, DollarPortListParameterSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m #(parameter int P = $);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DollarConstantElaboration, DollarSimpleBitVectorTypeParameterIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter logic [7:0] P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DollarConstantElaboration, DollarParameterUsableAsUnboundedRangeBound) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter r1 = 1;\n"
      "  parameter r2 = $;\n"
      "  logic clk, a, b, c;\n"
      "  property inq1;\n"
      "    @(posedge clk) a ##[r1:r2] b |=> c;\n"
      "  endproperty\n"
      "  assert property (inq1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_r2 = false;
  for (auto& p : mod->params) {
    if (p.name == "r2") {
      found_r2 = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_r2);
}

TEST(DollarConstantElaboration, BoundedParameterNotUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_unbounded);
    }
  }
}

TEST(DollarConstantElaboration, DollarParameterAssignedToAnotherIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter Q = $;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_p = false;
  for (auto& p : mod->params) {
    if (p.name == "Q") {
      EXPECT_TRUE(p.is_unbounded);
    }
    if (p.name == "P") {
      found_p = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_p);
}

TEST(DollarConstantElaboration, DollarPortListParameterChainIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m #(parameter Q = $, parameter P = Q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_p = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found_p = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_p);
}

TEST(DollarConstantElaboration, ParameterAssignedBoundedParameterNotUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter Q = 7;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_unbounded);
    }
  }
}

TEST(DollarConstantElaboration, DollarParameterChainThreeDeepAllUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter A = $;\n"
      "  parameter B = A;\n"
      "  parameter C = B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int seen = 0;
  for (auto& p : mod->params) {
    if (p.name == "A" || p.name == "B" || p.name == "C") {
      ++seen;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_EQ(seen, 3);
}

TEST(DollarConstantElaboration,
     DollarLocalparamReferencedByParameterIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam Q = $;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_p = false;
  for (auto& p : mod->params) {
    if (p.name == "Q") {
      EXPECT_TRUE(p.is_unbounded);
    }
    if (p.name == "P") {
      found_p = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_p);
}

TEST(DollarConstantElaboration, DollarLocalparamSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DollarConstantElaboration, NonSelfContainedDollarParameterIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = $ + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$' may only be assigned to parameter 'P' as a "
                            "complete, self-contained expression",
                            2, "6.20.7"));
}

TEST(DollarConstantElaboration, NonSelfContainedDollarPortParameterIsError) {
  ElabFixture f;
  Elaborate(
      "module m #(parameter int P = $ + 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$' may only be assigned to parameter 'P' as a "
                            "complete, self-contained expression",
                            1, "6.20.7"));
}

TEST(DollarConstantElaboration, DollarParameterNotResolved) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_resolved);
    }
  }
}

TEST(DollarConstantElaboration,
     DollarParameterOfAGenerateBlockDoesNotMakeAModuleLevelParameterUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam P = $;\n"
      "    end\n"
      "  endgenerate\n"
      "  localparam Q = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_q = false;
  for (auto& p : mod->params) {
    if (p.name != "Q" || !p.gen_block_prefix.empty()) continue;
    found_q = true;
    EXPECT_FALSE(p.is_unbounded)
        << "block 'a' localparam P should not reach a module-level Q";
  }
  EXPECT_TRUE(found_q);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'Q' initializer is not a constant expression", 7, "6.20.4"));
}

TEST(DollarConstantElaboration,
     DollarParameterOfAGenerateBlockStillReachesThatBlocksParameter) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam P = $;\n"
      "      localparam Q = P;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_q = false;
  for (auto& p : mod->params) {
    if (p.name != "Q") continue;
    found_q = true;
    EXPECT_TRUE(p.is_unbounded)
        << "block 'a' localparam P should reach block 'a' localparam Q";
  }
  EXPECT_TRUE(found_q);
}

TEST(DollarConstantElaboration, DollarClassParamDefaultIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(int N = $);\n"
             "endclass\n"
             "module t;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DollarConstantElaboration, DollarClassBodyLocalparamIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  localparam int N = $;\n"
             "endclass\n"
             "module t;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DollarConstantElaboration, DollarClassParamOverrideIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(int N = 4);\n"
             "endclass\n"
             "module t;\n"
             "  C #($) c;\n"
             "  class D extends C #($);\n"
             "  endclass\n"
             "endmodule\n"));
}

TEST(DollarConstantElaboration, OverrideNamingADollarParameterIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(int N = 4);\n"
             "endclass\n"
             "module t;\n"
             "  parameter int P = $;\n"
             "  C #(P) d;\n"
             "  class D extends C #(P);\n"
             "  endclass\n"
             "endmodule\n"));
}

template <size_t N>
void ExpectDollarTypeReported(
    const ElabFixture& f,
    const std::pair<uint32_t, std::string_view> (&params)[N]) {
  for (const auto& [line, name] : params) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("'$' may be assigned only to a parameter of a simple bit "
                    "vector type, and parameter '{}' is not one",
                    name),
        line, "6.20.7"));
  }
}

TEST(DollarConstantElaboration,
     DollarAssignedToEachSimpleBitVectorTypeIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef bit [7:0] octet_t;\n"
             "  parameter P0 = $;\n"
             "  parameter signed [3:0] P1 = $;\n"
             "  parameter logic [7:0] P2 = $;\n"
             "  parameter reg P3 = $;\n"
             "  parameter bit [3:0] P4 = $;\n"
             "  parameter byte P5 = $;\n"
             "  parameter shortint P6 = $;\n"
             "  parameter int P7 = $;\n"
             "  parameter longint P8 = $;\n"
             "  parameter integer P9 = $;\n"
             "  parameter time P10 = $;\n"
             "  parameter octet_t P11 = $;\n"
             "endmodule\n"));
}

TEST(DollarConstantElaboration,
     DollarAssignedToAnotherParameterTypeIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef enum {A, B} e_t;\n"
      "  typedef struct packed {bit a;} s_t;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  typedef int i_t;\n"
      "  typedef bit a_t [2];\n"
      "  class C;\n"
      "  endclass\n"
      "  parameter real R = $;\n"
      "  parameter string S = $;\n"
      "  parameter e_t E = $;\n"
      "  parameter s_t T = $;\n"
      "  parameter bit [1:0][3:0] M = $;\n"
      "  parameter nib_t [1:0] N = $;\n"
      "  parameter i_t [1:0] I = $;\n"
      "  parameter int U [2] = $;\n"
      "  parameter a_t D = $;\n"
      "  parameter C H = $;\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kParams[] = {
      {9, "R"},  {10, "S"}, {11, "E"}, {12, "T"}, {13, "M"},
      {14, "N"}, {15, "I"}, {16, "U"}, {17, "D"}, {18, "H"}};
  ExpectDollarTypeReported(f, kParams);
}

TEST(DollarConstantElaboration,
     DollarPortOrDollarParameterOfAnotherTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m #(parameter real R = $,\n"
      "           parameter int A [2] = $,\n"
      "           parameter W = $);\n"
      "  parameter real Q = W;\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kParams[] = {
      {1, "R"}, {2, "A"}, {4, "Q"}};
  ExpectDollarTypeReported(f, kParams);
}

TEST(DollarConstantElaboration, UnresolvedOrAbsentTypeIsNotJudged) {
  const TypedefMap kTypedefs;
  const std::unordered_map<std::string_view, std::vector<Expr*>> kDims;
  const std::unordered_set<std::string_view> kClasses = {"C"};
  const TypeShapeTables kTables{kTypedefs, kDims, kClasses};
  DataType missing;
  missing.kind = DataTypeKind::kNamed;
  missing.type_name = "missing_t";
  EXPECT_TRUE(IsSimpleBitVectorType(missing, kTables));
  DataType handle;
  handle.kind = DataTypeKind::kNamed;
  handle.type_name = "C";
  EXPECT_FALSE(IsSimpleBitVectorType(handle, kTables));
  ElabFixture f;
  ValidateUnboundedParamType({"W", nullptr, false, {}}, kTables, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DollarConstantElaboration, DollarParameterInAQueueContextIsRejected) {
  ElabFixture f;
  Elaborate(
      "parameter P = 1;\n"
      "module m;\n"
      "  parameter P = $;\n"
      "  parameter N = 2;\n"
      "  int q[$];\n"
      "  int b[$:P];\n"
      "  int c[P];\n"
      "  int d[];\n"
      "  int e[N];\n"
      "  int g[4];\n"
      "  int qq[$][$];\n"
      "  function automatic int f();\n"
      "    return q[P];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int lq[$:P];\n"
      "    q[P] = 1;\n"
      "    q = q[0:P-1];\n"
      "    q[$unit::P] = 1;\n"
      "    qq[0][N] = 1;\n"
      "    b[N] = 1;\n"
      "    g[N] = 1;\n"
      "    if (N inside {[0:P]}) g[0] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6U, 7U, 13U, 16U, 17U, 18U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "parameter 'P' holds '$', which a queue context "
                              "does not permit",
                              line, "6.20.7"));
  }
  for (uint32_t line : {19U, 20U, 21U, 22U, 23U}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), "holds '$'", line, "6.20.7"));
  }
}

TEST(DollarConstantElaboration, DollarAsAnOrdinaryOperandIsRejected) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  int x, y, q[$];\n"
      "  wire [7:0] w;\n"
      "  wire [7:0] v = $;\n"
      "  int z = $;\n"
      "  assign w = $;\n"
      "  function automatic int f();\n"
      "    return $;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = $;\n"
      "    y = $ + 1;\n"
      "    if (x == $) y = 0;\n"
      "    x = q[$];\n"
      "    y = q[$-1];\n"
      "    x = int'(y inside {[0:$]});\n"
      "    y = f();\n"
      "  end\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "'$' may stand only in a queue's dimension or select, a value range's "
      "bound";
  for (uint32_t line : {4U, 5U, 6U, 8U, 11U, 12U, 13U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.20.7"));
  }
  for (uint32_t line : {14U, 15U, 16U, 17U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.20.7"));
  }
}

}  // namespace
