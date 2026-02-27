// §21.2.1: The display and write tasks


#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"

#include "fixture_simulator.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
namespace {

// =============================================================================
// Phase 3: §21.2.1 FormatArg specifiers
// =============================================================================
TEST(FormatArg, DecimalUnsigned) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 42);
  EXPECT_EQ(FormatArg(val, 'd'), "42");
}

TEST(FormatArg, HexLeadingZeros) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0x0A);
  // %h for 8-bit value should be 2 hex digits.
  EXPECT_EQ(FormatArg(val, 'h'), "0a");
}

TEST(FormatArg, OctalLeadingZeros) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 5);
  // %o for 8-bit value: ceil(8/3) = 3 octal digits.
  EXPECT_EQ(FormatArg(val, 'o'), "005");
}

TEST(FormatArg, BinaryReturnsToString) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 4, 0b1010);
  EXPECT_EQ(FormatArg(val, 'b'), "1010");
}

TEST(FormatArg, StringFromAscii) {
  Arena arena;
  // 'A' = 0x41 = 65
  auto val = MakeLogic4VecVal(arena, 8, 65);
  EXPECT_EQ(FormatValueAsString(val), "A");
}

}  // namespace
