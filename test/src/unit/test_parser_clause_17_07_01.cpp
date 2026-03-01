// §17.7.1: Checker variable assignments

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

// =============================================================================
// §17.4 Checker variables
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithVariables) {
  auto* unit = Parse(R"(
    checker var_check;
      logic a, b;
      assign a = b;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

}  // namespace
