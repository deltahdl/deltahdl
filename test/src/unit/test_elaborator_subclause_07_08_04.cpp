#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IntegralIndexAssocArrayElaboration, AssocArrayByteIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[byte];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 8u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayIntIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 32u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayShortintIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[shortint];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 16u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayLongintIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[longint];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 64u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayIntegerIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[integer];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 32u);
}

TEST(IntegralIndexAssocArrayElaboration, NotStringIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_FALSE(v.is_string_index);
  EXPECT_FALSE(v.is_wildcard_index);
}

TEST(IntegralIndexAssocArrayElaboration, BuiltinIntIndexIsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_TRUE(v.is_assoc);
  EXPECT_TRUE(v.is_index_signed);
}

TEST(IntegralIndexAssocArrayElaboration, UnsignedTypedefIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit [4:1] UNibble;\n"
      "  int map[UNibble];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_TRUE(v.is_assoc);
  EXPECT_EQ(v.assoc_index_width, 4u);
  EXPECT_FALSE(v.is_index_signed);
}

TEST(IntegralIndexAssocArrayElaboration, SignedTypedefIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit signed [4:1] SNibble;\n"
      "  int map[SNibble];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_TRUE(v.is_assoc);
  EXPECT_EQ(v.assoc_index_width, 4u);
  EXPECT_TRUE(v.is_index_signed);
}

TEST(IntegralIndexAssocArrayElaboration, RealIndexExprIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  initial map[r] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            4, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration, ShortrealIndexExprIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  shortreal s;\n"
      "  initial map[s] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            4, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration, IntegerIndexExprLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  initial map[5] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegralIndexAssocArrayElaboration, RealLiteralIndexIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  initial map[3.7] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            3, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration, RealIndexInReadPositionIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  initial x = map[r];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            5, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration, ExplicitRealCastIndexLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  initial map[int'(r)] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegralIndexAssocArrayElaboration, InlinePackedDimensionIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int aa[bit[3:0]];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 4u);
  EXPECT_FALSE(vars[0].is_index_signed);
}

TEST(IntegralIndexAssocArrayElaboration, RealIndexInAForkArmIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  initial begin\n"
      "    fork\n"
      "      x = map[r];\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            7, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration,
     RealIndexInAnAssertionPassStatementIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = map[r];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            6, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration,
     RealIndexInAnAssertionFailStatementIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = map[r];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            6, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration, RealIndexInARandcaseItemIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  initial randcase 1: x = map[r]; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            5, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration,
     RealIndexInARandsequenceCodeBlockIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = map[r]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            7, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration,
     RealIndexInAForLoopInitializationIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (x = map[r]; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            6, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration, RealIndexInAForLoopStepIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; x = map[r]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            6, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration, RealIndexExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int n [int];\n"
      "  int a[2];\n"
      "  real r;\n"
      "  initial begin\n"
      "    n[r + 1.0] = 1;\n"
      "    n[a[0]] = 1;\n"
      "    n[new] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'n'",
                            6, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration, RealSelectCastAndCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int n [int];\n"
      "  real ra [2];\n"
      "  real r;\n"
      "  function real g(); return 1.0; endfunction\n"
      "  function void vf(); endfunction\n"
      "  initial begin\n"
      "    n[ra[0]] = 1;\n"
      "    n[real'(1)] = 1;\n"
      "    n[g()] = 1;\n"
      "    n[int'(r)] = 1;\n"
      "    n[vf()] = 1;\n"
      "    n[nofunc()] = 1;\n"
      "    n[r[0]] = 1;\n"
      "    n[-nofunc()] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kReport =
      "real or shortreal index is not allowed on integral-indexed associative "
      "array 'n'";
  for (uint32_t line = 8; line <= 10; ++line) {
    EXPECT_TRUE(ReportedError(diags, kReport, line, "7.8.4"));
  }
  for (uint32_t line = 11; line <= 15; ++line) {
    EXPECT_FALSE(ReportedError(diags, kReport, line, "7.8.4"));
  }
}

}  // namespace
