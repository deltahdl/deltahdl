#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(RealDataType, RealTypeWidths) {
  DataType dt;
  dt.kind = DataTypeKind::kReal;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
  dt.kind = DataTypeKind::kShortreal;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
  dt.kind = DataTypeKind::kRealtime;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

TEST(RealDataType, RealtimeSynonymousWithReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  realtime rt;\n"
      "  initial begin r = 0.0; rt = 0.0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool r_real = false;
  bool rt_real = false;
  for (const auto& v : mod->variables) {
    if (v.name == "r") r_real = v.is_real;
    if (v.name == "rt") rt_real = v.is_real;
  }
  EXPECT_TRUE(r_real);
  EXPECT_TRUE(rt_real);
}

TEST(RealDataType, RealNegedge_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a;\n"
      "  always @(negedge a)\n"
      "    $display(\"negedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(RealDataType, RealTypesNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kReal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kShortreal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kRealtime));
}

TEST(RealDataType, RealBitSelect_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire b;\n"
      "  assign b = a[2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(RealDataType, RealEdge_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  always @(posedge a)\n"
      "    $display(\"posedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(RealDataType, RealIndex_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire [3:0] b;\n"
      "  wire c;\n"
      "  assign c = b[a];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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

TEST(RealDataType, ShortrealBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  shortreal a = 1.0;\n"
      "  wire b;\n"
      "  assign b = a[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(RealDataType, RealAssign_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
