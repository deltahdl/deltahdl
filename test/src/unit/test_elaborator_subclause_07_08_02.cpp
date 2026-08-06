#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StringIndexAssocArrayElaboration, AssocDimElaboratesStringIndex) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
  EXPECT_TRUE(mod->variables[0].is_string_index);
}

TEST(StringIndexAssocArrayElaboration, NotWildcardIndex) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_FALSE(v.is_wildcard_index);
}

TEST(StringIndexAssocArrayElaboration, VectorElementType) {
  ElabFixture f;
  auto* design = Elaborate("module m; bit [7:0] aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_TRUE(v.is_assoc);
  EXPECT_TRUE(v.is_string_index);
  EXPECT_EQ(v.width, 8u);
}

// §7.8.2: a string literal index of any length is a valid index.
TEST(StringIndexAssocArrayElaboration, StringLiteralIndexNoError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial aa[\"key\"] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.8.2: a string-typed variable is a valid index.
TEST(StringIndexAssocArrayElaboration, StringVariableIndexNoError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  string s;\n"
      "  initial aa[s] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.8.2: indexing with a non-string literal is a different type and shall be
// reported as a type check error.
TEST(StringIndexAssocArrayElaboration, IntegerLiteralIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial aa[7] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.8.2: indexing with a variable of a non-string type is a type check error.
TEST(StringIndexAssocArrayElaboration, IntegerVariableIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int i;\n"
      "  initial aa[i] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.8.2: string literals of any length are valid indices, so the
// zero-length empty string literal is accepted without a type check error.
TEST(StringIndexAssocArrayElaboration, EmptyStringLiteralIndexNoError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial aa[\"\"] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.8.2: the illegal-index rule applies wherever the array is indexed, not
// only when it is the assignment target. A non-string index in a read (an
// index used as a source operand) is a type check error just the same.
TEST(StringIndexAssocArrayElaboration, IntegerLiteralIndexInReadIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  initial x = aa[7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
