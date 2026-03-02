// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

TEST(ParserSection18, RandomizeWithIdListAndConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  function void test();\n"
      "    this.randomize() with (x) { x > 0; x < y; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
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

TEST(ParserSection18, RandArrayInClassWithConstraint) {
  auto r = Parse(
      "class a;\n"
      "  rand int B[5];\n"
      "  constraint c { foreach (B[i]) B[i] == 5; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

}  // namespace
