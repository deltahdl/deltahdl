#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast.h"

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

// A real index is reported by the §11.5.1 select rule rather than under §6.12,
// and the report stands at the select's base `b`.
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
                            "real type used as index is illegal", 5, "11.5.1"));
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
                            "bit-select on real type is illegal", 4, "11.5.1"));
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
                            "bit-select on real type is illegal", 4, "11.5.1"));
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
                            "bit-select on real type is illegal", 4, "11.5.1"));
}

// §6.12: edge event controls are prohibited on every real-variable type, not
// only real. A posedge on a shortreal is rejected the same way.
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

// §6.12: bit-select references of real variables are prohibited for every
// real-variable type, so a bit-select of a realtime is rejected.
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
                            "bit-select on real type is illegal", 4, "11.5.1"));
}

// §6.12: a real index expression is prohibited in a part-select of a vector,
// just as in a bit-select. Here the real drives an indexed part-select (+:).
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
                            "real type used as index is illegal", 5, "11.5.1"));
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

}  // namespace
