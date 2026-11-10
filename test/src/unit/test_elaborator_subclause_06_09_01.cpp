#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(VectorSpecification, LittleEndianWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [0:7] x; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(VectorSpecification, ThirtyTwoBitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [31:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 32u);
}

TEST(VectorSpecification, NetAndVarSameWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [15:0] net_w;\n"
      "  logic [15:0] var_v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 1u);
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 16u);
  EXPECT_EQ(mod->variables[0].width, 16u);
}

TEST(VectorSpecification, NegativeRangeWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [-1:4] b; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 6u);
}

TEST(VectorSpecification, EqualMsbLsbWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [3:3] a; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(VectorSpecification, BitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; bit [7:0] b; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(VectorSpecification, RegVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; reg [7:0] r; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(VectorSpecification, ConstantExpressionRange) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [2+1:0] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(VectorSpecification, BothNegativeRangeWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [-1:-4] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(VectorSpecification, GuaranteedMinimumMaxLength) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [65535:0] big; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 65536u);
}

TEST(VectorSpecification, ParameterConstantRange) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; parameter P = 4; logic [P-1:0] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(VectorSpecification, LocalparamConstantRange) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m; localparam int HI = 5; localparam int LO = 2; logic [HI:LO] "
      "v; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(VectorSpecification, ConstantFunctionCallRange) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function automatic int w(); return 8; endfunction\n"
      "  logic [w()-1:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(VectorSpecification, XInRangeIsError) {
  ElabFixture f;
  Elaborate("module m; logic [1'bx:0] a; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension range shall not contain x or z",
                            1, "7.4.1"));
}

TEST(VectorSpecification, ZInRangeIsError) {
  ElabFixture f;
  Elaborate("module m; logic [1'bz:0] a; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension range shall not contain x or z",
                            1, "7.4.1"));
}

constexpr std::string_view kXzInRange =
    "packed dimension range shall not contain x or z";
constexpr std::string_view kNonConstantRange =
    "packed dimension range shall be a constant integer expression";

TEST(VectorSpecification, XOrZInRangeIsErrorOnANetAnUnpackedDimAndAnInterface) {
  ElabFixture f;
  Elaborate(
      "interface i;\n"
      "  logic [3:1'bx] a;\n"
      "endinterface\n"
      "module m;\n"
      "  wire [1'bx:0] w;\n"
      "  logic [3:0] u [1'bx:0];\n"
      "  i ii();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXzInRange, 2, "7.4.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXzInRange, 5, "7.4.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked dimension range shall not contain x or z",
                            6, "7.4.2"));
}

TEST(VectorSpecification, DISABLED_XOrZInRangeIsErrorInEveryPlace) {
  ElabFixture f;
  Elaborate(
      "package p;\n"
      "  logic [4'b1x01:0] a;\n"
      "endpackage\n"
      "class C;\n"
      "  logic [1'bx:0] a;\n"
      "endclass\n"
      "module m(input logic [1'bz:0] pa);\n"
      "  typedef logic [2'bx1:0] T;\n"
      "  struct packed { logic [1'bx:0] f; } s;\n"
      "  function logic [1'bz:0] fn();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    logic [1'bx:0] q;\n"
      "  end\n"
      "  C c;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2U, 5U, 7U, 8U, 9U, 10U, 13U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXzInRange, line, "7.4.1"));
  }
}

TEST(VectorSpecification, DISABLED_XOrZFromAParameterInRangeIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = 4'bx;\n"
      "  localparam Z = 1'bz;\n"
      "  logic [P:0] a;\n"
      "  logic [3:Z] b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXzInRange, 4, "7.4.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXzInRange, 5, "7.4.1"));
}

TEST(VectorSpecification, DISABLED_NonConstantOrRealBoundIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int n;\n"
      "  wire [3:0] w;\n"
      "  logic [n:0] a;\n"
      "  logic [w:0] b;\n"
      "  function int g();\n"
      "    return n;\n"
      "  endfunction\n"
      "  logic [g():0] c;\n"
      "  logic [$random:0] d;\n"
      "  logic [$time:0] e;\n"
      "  logic [3.0:0] h;\n"
      "  parameter real R = 2.0;\n"
      "  logic [R:0] k;\n"
      "  logic [3:0][n:0] l;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4U, 5U, 9U, 10U, 11U, 12U, 14U, 15U}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNonConstantRange, line, "7.4.1"));
  }
}

TEST(VectorSpecification, DISABLED_NonConstantBoundIsErrorInEveryPlace) {
  ElabFixture f;
  Elaborate(
      "package p;\n"
      "  int pn;\n"
      "  logic [pn:0] a;\n"
      "endpackage\n"
      "interface i;\n"
      "  int n;\n"
      "  logic [n:0] a;\n"
      "endinterface\n"
      "program q;\n"
      "  int n;\n"
      "  logic [n:0] a;\n"
      "endprogram\n"
      "class C;\n"
      "  int n;\n"
      "  logic [n:0] a;\n"
      "endclass\n"
      "module m(input logic [p::pn:0] pa);\n"
      "  int n;\n"
      "  wire [n:0] w;\n"
      "  typedef logic [n:0] T;\n"
      "  struct packed { logic [n:0] f; } s;\n"
      "  function logic [n:0] fn();\n"
      "  endfunction\n"
      "  if (1) begin : g\n"
      "    logic [n:0] b;\n"
      "  end\n"
      "  i ii();\n"
      "  q qq();\n"
      "  C c;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3U, 7U, 11U, 15U, 17U, 19U, 20U, 21U, 22U, 25U}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNonConstantRange, line, "7.4.1"));
  }
}

TEST(VectorSpecification, ConstantSystemFunctionBoundIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [$clog2(8):0] k;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

}  // namespace
