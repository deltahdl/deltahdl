#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RealDataType, RealNegedgeError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a;\n"
      "  always @(negedge a)\n"
      "    $display(\"negedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealTypesNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kReal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kShortreal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kRealtime));
}

TEST(RealDataType, RealPosedgeError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  always @(posedge a)\n"
      "    $display(\"posedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealIndexInBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire [3:0] b;\n"
      "  wire c;\n"
      "  assign c = b[a];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real type used as index is illegal", 5, "6.12"));
}

TEST(RealDataType, AllRealTypesElaborateWithIsReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  shortreal sr;\n"
      "  realtime rt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  EXPECT_TRUE(mod->variables[0].is_real) << "real";
  EXPECT_EQ(mod->variables[0].width, 64u) << "real width";
  EXPECT_TRUE(mod->variables[1].is_real) << "shortreal";
  EXPECT_EQ(mod->variables[1].width, 32u) << "shortreal width";
  EXPECT_TRUE(mod->variables[2].is_real) << "realtime";
  EXPECT_EQ(mod->variables[2].width, 64u) << "realtime width";
}

TEST(RealDataType, RealtimePosedgeError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  realtime a;\n"
      "  always @(posedge a)\n"
      "    $display(\"posedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealAssignmentOk) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(RealDataType, RealEdgeKeywordError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a;\n"
      "  always @(edge a)\n"
      "    $display(\"edge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire b;\n"
      "  assign b = a[2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealDataType, RealPartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire [3:0] b;\n"
      "  assign b = a[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealDataType, ShortrealBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  shortreal a = 1.0;\n"
      "  wire b;\n"
      "  assign b = a[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealDataType, ShortrealEdgeControlError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  shortreal a;\n"
      "  always @(posedge a)\n"
      "    $display(\"posedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealtimeBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  realtime a;\n"
      "  wire b;\n"
      "  assign b = a[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealDataType, RealIndexInPartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a = 1.0;\n"
      "  wire [7:0] b;\n"
      "  wire [1:0] c;\n"
      "  assign c = b[a +: 2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real type used as index is illegal", 5, "6.12"));
}

TEST(RealDataType, RealAndRealtimeInterchangeable) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  realtime rt;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    rt = r;\n"
      "    r = rt;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(RealDataType, RealEdgeInAProceduralEventControlError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r = 0.0;\n"
      "  initial begin\n"
      "    fork\n"
      "      @(posedge r) $display(\"edge\");\n"
      "      #1 r = 1.0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 5, "6.12"));
}

TEST(RealDataType, RealEdgeOnABlockLocalRealError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real m;\n"
      "  task tk;\n"
      "    real x;\n"
      "    @(m);\n"
      "    @(negedge x);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 6, "6.12"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(RealDataType, EdgeAndSelectOfARealInsideGenerateBlocksAreRejected) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "real r; logic y;", "always @(posedge r) y = 0;"},
      "edge event on real type is illegal", "6.12"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "real r; wire y;", "assign y = r[0];"},
      "bit-select of a real variable is illegal", "6.12"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "real r; logic y;", "initial y = r[0];"},
      "bit-select of a real variable is illegal", "6.12"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "real r; logic y;", "always @(r) y = 0;"}));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  real r;\n"
             "  logic y;\n"
             "  if (1) begin : g\n"
             "    logic [3:0] r;\n"
             "    initial y = r[0];\n"
             "  end\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [3:0] r;\n"
             "  logic y;\n"
             "  if (1) begin : g1\n"
             "    real r;\n"
             "  end\n"
             "  if (1) begin : g2\n"
             "    initial y = r[0];\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
