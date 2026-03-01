// §17.7: Checker variables

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

TEST_F(CheckerParseTest, CheckerWithBitVector) {
  auto* unit = Parse(R"(
    checker bv_check;
      logic [7:0] counter;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

}  // namespace
