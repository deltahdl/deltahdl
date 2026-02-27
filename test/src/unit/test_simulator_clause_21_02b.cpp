// §21.2: Display system tasks


#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"

#include "fixture_simulator.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
namespace {

TEST(FormatArg, StringFromAscii) {
  Arena arena;
  // 'A' = 0x41 = 65
  auto val = MakeLogic4VecVal(arena, 8, 65);
  EXPECT_EQ(FormatValueAsString(val), "A");
}

}  // namespace
