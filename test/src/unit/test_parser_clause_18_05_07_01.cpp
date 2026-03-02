// §18.5.7.1: foreach iterative constraints

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

// Constraint with foreach and nested constraint_set
TEST(SourceText, ConstraintForeach) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[10];\n"
      "  constraint fc {\n"
      "    foreach (arr[i]) {\n"
      "      arr[i] inside {[0:100]};\n"
      "    }\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "fc");
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
