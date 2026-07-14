

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
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
  EXPECT_TRUE(f.has_errors);
}

TEST(VectorNetAccessibility, ScalaredWithoutPackedDimIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire scalared w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.9.2: when scalared is used, bit-selects and part-selects of the net shall
// be permitted. A scalared vector net referenced by both a bit-select and a
// part-select elaborates without error.
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

// §6.9.2: an indexed part-select (the +: form) is a distinct part-select shape
// that a scalared net shall likewise permit.
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

// §6.9.2: the permission covers a bit-select used as a continuous-assignment
// target, a different syntactic position from a select read as an operand.
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

// §6.9.2: a part-select of a scalared net is also permitted in the
// assignment-target position.
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

// §6.9.2: the permit rule applies to any vector net type declared scalared;
// exercise it on the tri net family used in the standard's scalared example,
// built end-to-end from real net-declaration source (§6.7).
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
