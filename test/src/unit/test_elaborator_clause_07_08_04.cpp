#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

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

// §7.8.4: ordering and casting follow the signedness of the index type. The
// built-in integral index types are signed.
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

// §7.8.4: a typedef'd unsigned index type (bit without `signed`) orders
// unsigned, so its index is recorded as unsigned.
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

// §7.8.4: a typedef'd signed index type orders signed.
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

// §7.8.4: an implicit cast from a real expression to an integral index type is
// illegal. (A procedural index select; the continuous-assign real-select check
// does not cover procedural bodies.)
TEST(IntegralIndexAssocArrayElaboration, RealIndexExprIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  initial map[r] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.4: the prohibition on an implicit cast covers shortreal as well as real.
TEST(IntegralIndexAssocArrayElaboration, ShortrealIndexExprIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  shortreal s;\n"
      "  initial map[s] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.4: an integral index expression is legal and casts cleanly.
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

// §7.8.4: the illegal-implicit-cast rule covers a real *literal* index, not
// only a real-typed variable — a distinct input form that reaches the check by
// literal kind rather than by variable type.
TEST(IntegralIndexAssocArrayElaboration, RealLiteralIndexIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  initial map[3.7] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.4: the prohibition applies wherever the array is indexed, including a
// read (an index select on the right-hand side), not just a write target.
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
  EXPECT_TRUE(f.has_errors);
}

// §7.8.4: only the *implicit* cast from real is illegal. An explicit cast of a
// real value to an integral type (§6.24.1) yields an integral index and is
// legal, so wrapping the real operand in int'(...) defeats the prohibition.
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

}  // namespace
