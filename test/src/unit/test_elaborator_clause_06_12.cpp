#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(TypeEval, RealTypeWidths) {
  DataType dt;
  dt.kind = DataTypeKind::kReal;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
  dt.kind = DataTypeKind::kShortreal;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
  dt.kind = DataTypeKind::kRealtime;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

TEST(Elaboration, RealtimeSynonymousWithReal) {
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

TEST(Elaboration, RealNegedge_Error) {
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

TEST(TypeEval, RealTypesNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kReal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kShortreal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kRealtime));
}

TEST(Elaboration, RealBitSelect_Error) {
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

TEST(Elaboration, RealEdge_Error) {
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

TEST(Elaboration, RealAssign_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabA87, NumberRealElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real x;\n"
      "  initial x = 3.14;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
