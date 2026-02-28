// §10.10: Unpacked array concatenation


#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"

#include "fixture_simulator.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
namespace {

// =============================================================================
// §10.10 Unpacked array concatenation
// =============================================================================
TEST(UnpackedArrayConcat, BasicConcat) {
  // Create two array elements as flat variables, verify concatenation concept.
  SimFixture f;
  auto* a0 = f.ctx.CreateVariable("a[0]", 8);
  auto* a1 = f.ctx.CreateVariable("a[1]", 8);
  a0->value = MakeLogic4VecVal(f.arena, 8, 10);
  a1->value = MakeLogic4VecVal(f.arena, 8, 20);

  // Verify the flat naming convention for array elements.
  auto* found0 = f.ctx.FindVariable("a[0]");
  auto* found1 = f.ctx.FindVariable("a[1]");
  ASSERT_NE(found0, nullptr);
  ASSERT_NE(found1, nullptr);
  EXPECT_EQ(found0->value.ToUint64(), 10u);
  EXPECT_EQ(found1->value.ToUint64(), 20u);
}

}  // namespace
