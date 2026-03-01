// §24.7: Program control tasks

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// =============================================================================
// §24.5 $exit system task in programs
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithExitCall) {
  auto* unit = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $exit;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

}  // namespace
