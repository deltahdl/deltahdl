// §18.4.1: Rand modifier

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

// =============================================================================
// §18 Constrained random — parsing
// =============================================================================
// --- Multi-declarator rand properties (§18.4) ---
TEST(ParserSection18, RandMultiDeclarator) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_GE(r.cu->classes[0]->members.size(), 3u);
}

// --- Rand array property in class (§18.5.8.1) ---
TEST(ParserSection18, RandArrayInClass) {
  auto r = Parse(
      "class a;\n"
      "  rand int B[5];\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_GE(r.cu->classes[0]->members.size(), 1u);
}

TEST(ParserSection8, ClassWithQualifiersStaticRand) {
  auto r = Parse(
      "class MyClass;\n"
      "  local int secret;\n"
      "  protected int hidden;\n"
      "  static int shared;\n"
      "  rand int random_val;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 4u);
  EXPECT_TRUE(cls->members[2]->is_static);
  EXPECT_TRUE(cls->members[3]->is_rand);
}

}  // namespace
