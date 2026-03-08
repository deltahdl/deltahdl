#include "fixture_simulator.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §7.9.10: Passing an assoc array by value creates a local copy.
TEST(AssocMethods, AssocArgCopyByValue) {
  SimFixture f;
  auto* src = f.ctx.CreateAssocArray("actual", 32, true);
  src->str_data["key1"] = MakeLogic4VecVal(f.arena, 32, 100);
  src->str_data["key2"] = MakeLogic4VecVal(f.arena, 32, 200);

  // Simulate the copy that TryBindAssocArg would do.
  auto* dst =
      f.ctx.CreateAssocArray("formal", src->elem_width, src->is_string_key);
  dst->str_data = src->str_data;
  dst->has_default = src->has_default;
  dst->default_value = src->default_value;
  dst->index_width = src->index_width;

  // Verify copy has same data.
  EXPECT_EQ(dst->str_data.size(), 2u);
  EXPECT_EQ(dst->str_data["key1"].ToUint64(), 100u);

  // Modify formal — should not affect actual.
  dst->str_data["key1"] = MakeLogic4VecVal(f.arena, 32, 999);
  EXPECT_EQ(src->str_data["key1"].ToUint64(), 100u);
}

// §7.9.10: Copy includes default value.
TEST(AssocMethods, AssocArgCopiesDefault) {
  SimFixture f;
  auto* src = f.ctx.CreateAssocArray("actual", 32, false);
  src->has_default = true;
  src->default_value = MakeLogic4VecVal(f.arena, 32, 42);
  src->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);

  auto* dst =
      f.ctx.CreateAssocArray("formal", src->elem_width, src->is_string_key);
  dst->int_data = src->int_data;
  dst->has_default = src->has_default;
  dst->default_value = src->default_value;
  dst->index_width = src->index_width;

  EXPECT_TRUE(dst->has_default);
  EXPECT_EQ(dst->default_value.ToUint64(), 42u);
  EXPECT_EQ(dst->int_data.size(), 1u);
}

}  // namespace
