#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(VectorNetAccessibility, VectoredNetElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire vectored [31:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 32u);
}

TEST(VectorNetAccessibility, ScalaredNetElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri1 scalared [63:0] bus64;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 64u);
}

TEST(VectorNetAccessibility, VectoredWithPackedDimOk) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(VectorNetAccessibility, ScalaredWithPackedDimOk) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(VectorNetAccessibility, VectoredWithoutPackedDimIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire vectored w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "vectored or scalared requires at least one packed dimension", 2,
      "6.9.2"));
}

TEST(VectorNetAccessibility, ScalaredWithoutPackedDimIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire scalared w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "vectored or scalared requires at least one packed dimension", 2,
      "6.9.2"));
}

TEST(VectorNetAccessibility, ScalaredPermitsBitAndPartSelects) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire scalared [7:0] s;\n"
      "  wire        b;\n"
      "  wire [3:0]  p;\n"
      "  assign b = s[2];\n"
      "  assign p = s[6:3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VectorNetAccessibility, ScalaredPermitsIndexedPartSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire scalared [7:0] s;\n"
      "  wire [1:0]  p;\n"
      "  assign p = s[3 +: 2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VectorNetAccessibility, ScalaredPermitsBitSelectAsAssignTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire scalared [7:0] s;\n"
      "  wire        b;\n"
      "  assign s[2] = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VectorNetAccessibility, ScalaredPermitsPartSelectAsAssignTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire scalared [7:0] s;\n"
      "  wire [3:0]  p;\n"
      "  assign s[6:3] = p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VectorNetAccessibility, ScalaredTriNetPermitsSelects) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri scalared [7:0] t;\n"
      "  wire        b;\n"
      "  wire [3:0]  p;\n"
      "  assign b = t[0];\n"
      "  assign p = t[3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
