// §17.5: Checker procedures

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

// =============================================================================
// §17.5 Checker procedures (always, initial)
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithAlwaysBlock) {
  auto* unit = Parse(R"(
    checker always_check(input logic clk, input logic a);
      always @(posedge clk)
        assert(a);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kAlwaysBlock));
}

TEST_F(CheckerParseTest, CheckerWithInitialBlock) {
  auto* unit = Parse(R"(
    checker init_check;
      initial begin
        $display("checker started");
      end
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

}  // namespace
