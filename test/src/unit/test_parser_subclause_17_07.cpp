#include "fixture_parser.h"

using namespace delta;

namespace {

// §17.7: a checker variable may carry an optional rand qualifier, which makes
// it a free variable. The parser records the qualifier on the declaration.
TEST(CheckerVariables, RandQualifierMarksCheckerVariable) {
  auto r = Parse(
      "checker chk;\n"
      "  rand bit flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  bool saw_rand = false;
  for (const auto* item : r.cu->checkers[0]->items) {
    if (item->is_rand) saw_rand = true;
  }
  EXPECT_TRUE(saw_rand);
}

// §17.7: an ordinary (non-rand) checker variable carries no free-variable
// qualifier.
TEST(CheckerVariables, PlainCheckerVariableIsNotRand) {
  auto r = Parse(
      "checker chk;\n"
      "  bit flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  for (const auto* item : r.cu->checkers[0]->items) {
    EXPECT_FALSE(item->is_rand);
  }
}

// §17.7: a free variable declaration may additionally carry a const qualifier,
// producing a constant free variable.
TEST(CheckerVariables, ConstFreeVariableParses) {
  EXPECT_TRUE(
      ParseOk("checker chk;\n"
              "  rand const bit [5:0] idx;\n"
              "endchecker\n"));
}

// §17.7: a variable defined in a checker body shall have a static lifetime, so
// an explicit automatic lifetime on a checker variable is rejected.
TEST(CheckerVariables, AutomaticCheckerVariableIsIllegal) {
  auto r = Parse(
      "checker chk;\n"
      "  automatic bit flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
