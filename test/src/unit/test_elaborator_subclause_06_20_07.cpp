#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <format>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/simple_bit_vector.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_config_params.h"
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
     DollarAssignedToAClassParameterOfAnotherTypeIsRejected) {
  ElabFixture f;
  Elaborate(
      "class C #(real R = $, string S = $, bit [1:0][3:0] M = $,\n"
      "          int U [2] = $);\n"
      "  localparam real L = $;\n"
      "  class N #(shortreal Q = $);\n"
      "  endclass\n"
      "endclass\n"
      "class E #(real F = 1.0, int I = 1);\n"
      "endclass\n"
      "package p;\n"
      "  class K;\n"
      "    localparam real P = $;\n"
      "    E #($) h;\n"
      "  endclass\n"
      "endpackage\n"
      "interface i;\n"
      "  class G #(real V = $);\n"
      "  endclass\n"
      "endinterface\n"
      "module m;\n"
      "  class D extends E #(.F($));\n"
      "    localparam string T = $;\n"
      "  endclass\n"
      "  E #($, $) e;\n"
      "  E #(.I($)) d;\n"
      "  if (1) begin : g\n"
      "    class H #(real W = $);\n"
      "    endclass\n"
      "  end\n"
      "endmodule\n"
      "typedef real r_t;\n"
      "class Z #(r_t X = $);\n"
      "endclass\n"
      "E #($) uv;\n"
      "package q;\n"
      "  E #(.F($)) pv;\n"
      "endpackage\n",
      f);
  const std::pair<uint32_t, std::string_view> kParams[] = {
      {1, "R"},  {1, "S"},  {1, "M"},  {2, "U"},  {3, "L"},  {4, "Q"},
      {11, "P"}, {12, "F"}, {16, "V"}, {20, "F"}, {21, "T"}, {23, "F"},
      {26, "W"}, {31, "X"}, {33, "F"}, {35, "F"}};
  ExpectDollarTypeReported(f, kParams);
  constexpr std::string_view kMessage =
      "'$' may be assigned only to a parameter of a simple bit vector type";
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, 24, "6.20.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'$' may be assigned only to a parameter of a "
                             "simple bit vector type, and parameter 'I' is "
                             "not one",
                             23, "6.20.7"));
}

TEST(DollarConstantElaboration,
     DollarAssignedToAClassParameterOfASimpleBitVectorTypeIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(int R = $, S = $, bit [3:0] M = $,\n"
             "          logic signed [7:0] U = $);\n"
             "  localparam integer L = $;\n"
             "  class N #(byte Q = $);\n"
             "  endclass\n"
             "endclass\n"
             "class E #(int F = 1, real I = 1.0);\n"
             "endclass\n"
             "package p;\n"
             "  class K;\n"
             "    localparam longint P = $;\n"
             "    E #($) h;\n"
             "  endclass\n"
             "endpackage\n"
             "interface i;\n"
             "  class G #(time V = $);\n"
             "  endclass\n"
             "endinterface\n"
             "module m;\n"
             "  class D extends E #(.F($));\n"
             "    localparam shortint T = $;\n"
             "  endclass\n"
             "  E #($) e;\n"
             "  if (1) begin : g\n"
             "    class H #(reg W = $);\n"
             "    endclass\n"
             "  end\n"
             "endmodule\n"
             "typedef bit [7:0] b_t;\n"
             "class Z #(b_t X = $);\n"
             "endclass\n"
             "E #($) uv;\n"
             "package q;\n"
             "  E #(.F($)) pv;\n"
             "endpackage\n"));
}

TEST(DollarConstantElaboration, NonSelfContainedDollarClassParameterIsError) {
  ElabFixture f;
  Elaborate(
      "class C #(int N = $ + 1);\n"
      "  localparam int L = $ - 1;\n"
      "  class I #(int J = -$);\n"
      "  endclass\n"
      "endclass\n"
      "class E #(int N = 1, int M = 1);\n"
      "endclass\n"
      "package p;\n"
      "  class K;\n"
      "    localparam int P = $ * 2;\n"
      "    E #($ * 2) h;\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  class D extends E #(.M($ + 1));\n"
      "    localparam int T = $ ? 1 : 0;\n"
      "  endclass\n"
      "  E #(1, 2 + $) e;\n"
      "  if (1) begin : g\n"
      "    class G #(int F = $ + $);\n"
      "    endclass\n"
      "  end\n"
      "endmodule\n"
      "E #($ + 1) uv;\n"
      "package q;\n"
      "  E #(.N(1 - $)) pv;\n"
      "endpackage\n",
      f);
  const std::pair<uint32_t, std::string_view> kParams[] = {
      {1, "N"},  {2, "L"},  {3, "J"},  {10, "P"}, {11, "N"}, {15, "M"},
      {16, "T"}, {18, "M"}, {20, "F"}, {24, "N"}, {26, "N"}};
  for (const auto& [line, name] : kParams) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("'$' may only be assigned to parameter '{}' as a "
                    "complete, self-contained expression",
                    name),
        line, "6.20.7"))
        << line;
  }
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    EXPECT_EQ(diag.message.find("not a constant expression"), std::string::npos)
        << diag.message;
  }
}

TEST(DollarConstantElaboration, SelfContainedDollarClassParameterIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(int N = $);\n"
             "  localparam int L = $;\n"
             "  class I #(int J = $);\n"
             "  endclass\n"
             "endclass\n"
             "class E #(int N = 1, int M = 1);\n"
             "endclass\n"
             "package p;\n"
             "  class K;\n"
             "    localparam int P = $;\n"
             "    E #($) h;\n"
             "  endclass\n"
             "endpackage\n"
             "module m;\n"
             "  class D extends E #(.M($));\n"
             "    localparam int T = $;\n"
             "  endclass\n"
             "  E #(1, $) e;\n"
             "  if (1) begin : g\n"
             "    class G #(int F = $);\n"
             "    endclass\n"
             "  end\n"
             "endmodule\n"
             "E #($) uv;\n"
             "package q;\n"
             "  E #(.N($)) pv;\n"
             "endpackage\n"));
}

bool ChildParamUnbounded(const RtlirModule* top, std::string_view inst,
                         std::string_view param) {
  for (const auto& child : top->children) {
    if (child.simple_inst_name != inst || child.resolved == nullptr) continue;
    for (const auto& p : child.resolved->params) {
      if (p.name == param) return p.is_unbounded;
    }
  }
  return false;
}

TEST(DollarConstantElaboration,
     DollarOverrideOfAnInstanceParameterOfAnotherTypeIsRejected) {
  ElabFixture f;
  Elaborate(
      "module s #(parameter real R = 1.0, parameter int N = 1);\n"
      "endmodule\n"
      "module b;\n"
      "  parameter real R = 1.0;\n"
      "  parameter string S = \"x\";\n"
      "endmodule\n"
      "interface i #(parameter real R = 1.0);\n"
      "endinterface\n"
      "program p #(parameter shortreal R = 1.0);\n"
      "endprogram\n"
      "module m;\n"
      "  s #(.R($)) u1();\n"
      "  s #($, $) u2();\n"
      "  b #(.R($), .S($)) u3();\n"
      "  i #($) u4();\n"
      "  p #(.R($)) u5();\n"
      "  if (1) begin : g\n"
      "    s #(.R($)) u6();\n"
      "  end\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kParams[] = {
      {12, "R"}, {13, "R"}, {14, "R"}, {14, "S"},
      {15, "R"}, {16, "R"}, {18, "R"}};
  ExpectDollarTypeReported(f, kParams);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'$' may be assigned only to a parameter of a "
                             "simple bit vector type, and parameter 'N' is "
                             "not one",
                             13, "6.20.7"));
}

TEST(DollarConstantElaboration,
     DollarOverrideOfAnInstanceParameterOfASimpleBitVectorTypeIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module s #(parameter int N = 1, parameter M = 1,\n"
      "           parameter bit [3:0] B = 1);\n"
      "endmodule\n"
      "module b;\n"
      "  parameter logic [7:0] L = 1;\n"
      "  parameter integer I = 1;\n"
      "endmodule\n"
      "interface i #(parameter int N = 1);\n"
      "endinterface\n"
      "program p #(parameter longint N = 1);\n"
      "endprogram\n"
      "module m;\n"
      "  s #(.N($), .M($), .B($)) u1();\n"
      "  s #($, 2) u2();\n"
      "  b #(.L($), .I($)) u3();\n"
      "  i #($) u4();\n"
      "  p #(.N($)) u5();\n"
      "  if (1) begin : g\n"
      "    s #(.N($)) u6();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* top = design->top_modules[0];
  const std::pair<std::string_view, std::string_view> kUnbounded[] = {
      {"u1", "N"}, {"u1", "M"}, {"u1", "B"}, {"u2", "N"}, {"u3", "L"},
      {"u3", "I"}, {"u4", "N"}, {"u5", "N"}, {"u6", "N"}};
  for (const auto& [inst, param] : kUnbounded) {
    EXPECT_TRUE(ChildParamUnbounded(top, inst, param)) << inst << "." << param;
  }
  EXPECT_FALSE(ChildParamUnbounded(top, "u2", "M"));
}

TEST(DollarConstantElaboration, NonSelfContainedDollarOverrideIsError) {
  ElabFixture f;
  Elaborate(
      "module s #(parameter int N = 1, parameter int M = 1);\n"
      "endmodule\n"
      "module b;\n"
      "  parameter int K = 1;\n"
      "endmodule\n"
      "module m;\n"
      "  s #(.N($ + 1)) u1();\n"
      "  s #(1, $ - 1) u2();\n"
      "  b #(.K(-$)) u3();\n"
      "  if (1) begin : g\n"
      "    s #(.M($ * 2)) u4();\n"
      "  end\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kParams[] = {
      {7, "N"}, {8, "M"}, {9, "K"}, {11, "M"}};
  for (const auto& [line, name] : kParams) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("'$' may only be assigned to parameter '{}' as a "
                    "complete, self-contained expression",
                    name),
        line, "6.20.7"))
        << line;
  }
}

TEST(DollarConstantElaboration, DollarConfigurationOverrideIsJudged) {
  ElabFixture f;
  ConfigElab(f,
             "module c #(parameter real R = 1.0, parameter int N = 1,\n"
             "           parameter int M = 1);\n"
             "endmodule\n"
             "module top; c u(); endmodule\n"
             "config cfg;\n"
             "  design top;\n"
             "  instance top.u use #(.R($), .N($ + 1), .M($));\n"
             "endconfig\n");
  const std::pair<uint32_t, std::string_view> kParams[] = {{7, "R"}};
  ExpectDollarTypeReported(f, kParams);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$' may only be assigned to parameter 'N' as a "
                            "complete, self-contained expression",
                            7, "6.20.7"));
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    EXPECT_EQ(diag.message.find("has no constant value"), std::string::npos)
        << diag.message;
  }
}

TEST(DollarConstantElaboration, DollarConfigurationOverrideIsUnbounded) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(f,
                                 "module c #(parameter int N = 1);\n"
                                 "endmodule\n"
                                 "module top; c u(); endmodule\n"
                                 "config cfg;\n"
                                 "  design top;\n"
                                 "  instance top.u use #(.N($));\n"
                                 "endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  bool found = false;
  for (const auto& p : u->params) {
    if (p.name != "N") continue;
    found = true;
    EXPECT_TRUE(p.is_unbounded);
  }
  EXPECT_TRUE(found);
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
