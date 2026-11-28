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

TEST(VectorSpecification, XOrZInRangeIsErrorInEveryPlace) {
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

TEST(VectorSpecification, XOrZFromAParameterInRangeIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = 4'bx;\n"
      "  localparam Z = 1'bz;\n"
      "  logic [P:0] a;\n"
      "  logic [3:Z] b;\n"
      "  parameter bit [3:0] B = 4'bx;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  localparam nib_t N = 4'bz;\n"
      "  parameter K = 4'b0011;\n"
      "  logic [B:0] c;\n"
      "  logic [N:0] d;\n"
      "  logic [K:0] e;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXzInRange, 4, "7.4.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXzInRange, 5, "7.4.1"));
  for (uint32_t line : {10U, 11U, 12U}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), line)) << line;
  }
}

TEST(VectorSpecification, XOrZFromAConstantInRangeIsErrorInEveryPlace) {
  ElabFixture f;
  Elaborate(
      "parameter CU = 1'bx;\n"
      "logic [CU:0] cu;\n"
      "package p;\n"
      "  parameter PP = 2'bx1;\n"
      "  logic [PP:0] a;\n"
      "  parameter PQ = PP + 1;\n"
      "  logic [PQ:0] c;\n"
      "endpackage\n"
      "package p2;\n"
      "  import p::*;\n"
      "  logic [PP:0] a;\n"
      "endpackage\n"
      "class C #(parameter CP = 1'bz);\n"
      "  localparam CL = 1'bx;\n"
      "  logic [CP:0] a;\n"
      "  logic [CL:0] b;\n"
      "  localparam CM = CP + 1;\n"
      "  logic [CM:0] c;\n"
      "endclass\n"
      "class D;\n"
      "  localparam DL = 1'bx;\n"
      "endclass\n"
      "interface i;\n"
      "  localparam L = 'x;\n"
      "  logic [L:0] a;\n"
      "endinterface\n"
      "program q;\n"
      "  localparam L = 'z;\n"
      "  logic [L:0] a;\n"
      "endprogram\n"
      "module m #(parameter H = 1'bx)\n"
      "    (input logic [H:0] pa);\n"
      "  import p::*;\n"
      "  localparam Q = H + 1;\n"
      "  wire [Q:0] w;\n"
      "  logic [3:0] u [Q:0];\n"
      "  typedef logic [p::PP:0] T;\n"
      "  struct packed { logic [H:0] f; } s;\n"
      "  function logic [H:0] fn();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    logic [H:0] v;\n"
      "  end\n"
      "  if (1) begin : g\n"
      "    localparam G = 1'bz;\n"
      "    logic [G:0] b;\n"
      "  end\n"
      "  logic [PP:0] k;\n"
      "  logic [$unit::CU:0] n;\n"
      "  logic [D::DL:0] r;\n"
      "  i ii();\n"
      "  q qq();\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2U, 5U, 7U, 11U, 15U, 16U, 18U, 25U, 29U, 32U, 35U, 37U,
                        38U, 39U, 42U, 46U, 48U, 49U, 50U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXzInRange, line, "7.4.1"))
        << line;
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked dimension range shall not contain x or z",
                            36, "7.4.2"));
}

TEST(VectorSpecification, KnownConstantInRangeIsAcceptedInEveryPlace) {
  ElabFixture f;
  Elaborate(
      "parameter CU = 1'b1;\n"
      "logic [CU:0] cu;\n"
      "package p;\n"
      "  parameter PP = 2'b01;\n"
      "  parameter bit PB = 1'bx;\n"
      "  logic [PP:0] a;\n"
      "  logic [PB:0] b;\n"
      "  parameter PQ = PP + 1;\n"
      "  logic [PQ:0] c;\n"
      "endpackage\n"
      "package p2;\n"
      "  import p::*;\n"
      "  logic [PP:0] a;\n"
      "endpackage\n"
      "class C #(parameter CP = 1'b1);\n"
      "  localparam int CL = 1'bx;\n"
      "  logic [CP:0] a;\n"
      "  logic [CL:0] b;\n"
      "  localparam CM = CP + 1;\n"
      "  logic [CM:0] c;\n"
      "endclass\n"
      "class D;\n"
      "  localparam int DL = 'x;\n"
      "endclass\n"
      "module m #(parameter H = 1'b1, parameter bit HB = 1'bz)\n"
      "    (input logic [H:0] pa);\n"
      "  import p::*;\n"
      "  localparam Q = H + HB;\n"
      "  wire [Q:0] w;\n"
      "  logic [3:0] u [Q:0];\n"
      "  if (1) begin : g\n"
      "    localparam G = 1'b0;\n"
      "    logic [G:0] b;\n"
      "  end\n"
      "  logic [PB:0] k;\n"
      "  logic [p::PP:0] n;\n"
      "  logic [D::DL:0] r;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(VectorSpecification, XOrZFromAnOverriddenParameterInRangeIsError) {
  ElabFixture f;
  Elaborate(
      "module literal_override #(parameter P = 3);\n"
      "  logic [P:0] a;\n"
      "endmodule\n"
      "module parent_override #(parameter P = 3);\n"
      "  logic [P:0] a;\n"
      "endmodule\n"
      "module known_override #(parameter P = 1'bx);\n"
      "  logic [P:0] a;\n"
      "endmodule\n"
      "module body_override;\n"
      "  parameter P = 3;\n"
      "  logic [P:0] a;\n"
      "endmodule\n"
      "module m;\n"
      "  localparam X = 1'bz;\n"
      "  literal_override #(4'bx) o();\n"
      "  parent_override #(.P(X)) n();\n"
      "  known_override #(.P(3)) k();\n"
      "  body_override #(.P(2'bx0)) b();\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2U, 5U, 12U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXzInRange, line, "7.4.1"))
        << line;
  }
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 8));
}

TEST(VectorSpecification, NonConstantOrRealBoundIsError) {
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
      "  typedef logic [3:0] U;\n"
      "  U [n:0] o;\n"
      "  typedef enum logic [1:0] { A, B } E;\n"
      "  E [n:0] q;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4U, 5U, 9U, 10U, 11U, 12U, 14U, 15U, 17U, 19U}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNonConstantRange, line, "7.4.1"));
  }
}

TEST(VectorSpecification, NonConstantBoundIsErrorInEveryPlace) {
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

TEST(VectorSpecification,
     NonConstantBoundIsErrorInTheUnitAProcedureAndAClassMethod) {
  ElabFixture f;
  Elaborate(
      "int cn;\n"
      "logic [cn:0] cu;\n"
      "class D;\n"
      "  int n;\n"
      "  function logic [n:0] get();\n"
      "    logic [n:0] r;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int n;\n"
      "  initial begin\n"
      "    logic [n:0] q;\n"
      "  end\n"
      "  task t;\n"
      "    logic [n:0] k;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2U, 5U, 6U, 12U, 15U}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNonConstantRange, line, "7.4.1"));
  }
}

TEST(VectorSpecification, NonConstantBoundIsErrorInANestedOrLaterMemberDim) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int n;\n"
      "  localparam int K = 3;\n"
      "  struct packed { struct packed { logic [n:0] g; } h; } s;\n"
      "  struct packed { logic [K:0][n:0] f; } t;\n"
      "  struct packed { struct packed { logic [K:0] g; } h; } u;\n"
      "  struct packed { logic [K:0][1:0] f; } v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNonConstantRange, 4, "7.4.1"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNonConstantRange, 5, "7.4.1"));
  for (uint32_t line : {6U, 7U}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNonConstantRange, line, "7.4.1"));
  }
}

TEST(VectorSpecification, RealParameterBoundIsErrorInAPackageAndTheUnit) {
  ElabFixture f;
  Elaborate(
      "parameter real CR = 2.0;\n"
      "logic [CR:0] cu;\n"
      "parameter CI = 2;\n"
      "logic [CI:0] ci;\n"
      "package p;\n"
      "  parameter real PR = 2.0;\n"
      "  parameter PU = 1.5;\n"
      "  parameter PK = 3;\n"
      "  logic [PR:0] a;\n"
      "  logic [PU:0] b;\n"
      "  logic [PK:0] c;\n"
      "endpackage\n",
      f);
  for (uint32_t line : {2U, 9U, 10U}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNonConstantRange, line, "7.4.1"));
  }
  for (uint32_t line : {4U, 11U}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNonConstantRange, line, "7.4.1"));
  }
}

TEST(VectorSpecification, ScopedOrTypedefBoundIsCheckedInAPackageAndAClass) {
  ElabFixture f;
  Elaborate(
      "package q;\n"
      "  int qn;\n"
      "  localparam int QK = 3;\n"
      "endpackage\n"
      "package p;\n"
      "  logic [q::qn:0] a;\n"
      "  logic [q::QK:0] b;\n"
      "endpackage\n"
      "class C;\n"
      "  int n;\n"
      "  localparam int K = 3;\n"
      "  logic [q::qn:0] a;\n"
      "  logic [q::QK:0] b;\n"
      "  typedef logic [n:0] T;\n"
      "  typedef logic [K:0] U;\n"
      "endclass\n",
      f);
  for (uint32_t line : {6U, 12U, 14U}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNonConstantRange, line, "7.4.1"));
  }
  for (uint32_t line : {7U, 13U, 15U}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNonConstantRange, line, "7.4.1"));
  }
}

TEST(VectorSpecification, ClassScopedParameterBoundIsAccepted) {
  ElabFixture f;
  Elaborate(
      "class C;\n"
      "  localparam int K = 3;\n"
      "endclass\n"
      "module m;\n"
      "  logic [C::K:0] a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(VectorSpecification, ConstantBoundIsAcceptedInEveryPlace) {
  ElabFixture f;
  Elaborate(
      "parameter int CK = 2;\n"
      "logic [CK:0] cu;\n"
      "package p;\n"
      "  parameter int PK = 3;\n"
      "  logic [PK:0] a;\n"
      "  typedef logic [PK:0] PT;\n"
      "endpackage\n"
      "interface i;\n"
      "  localparam int K = 3;\n"
      "  logic [K:0] a;\n"
      "endinterface\n"
      "program q;\n"
      "  localparam int K = 3;\n"
      "  logic [K:0] a;\n"
      "endprogram\n"
      "class C;\n"
      "  localparam int K = 3;\n"
      "  logic [K:0] a;\n"
      "  function logic [K:0] get();\n"
      "    logic [K:0] r;\n"
      "    return r;\n"
      "  endfunction\n"
      "endclass\n"
      "module m(input logic [p::PK:0] pa);\n"
      "  localparam int K = 3;\n"
      "  wire [K:0] w;\n"
      "  typedef logic [K:0] T;\n"
      "  struct packed { logic [K:0] f; } s;\n"
      "  function logic [K:0] fn();\n"
      "    return '0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    logic [$clog2(K):0] v;\n"
      "  end\n"
      "  if (1) begin : g\n"
      "    logic [K:0] b;\n"
      "  end\n"
      "  i ii();\n"
      "  q qq();\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
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
