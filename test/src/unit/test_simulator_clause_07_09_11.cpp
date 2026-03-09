#include "fixture_simulator.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(AssocMethods, LiteralInitIntKeys) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[2] = MakeLogic4VecVal(f.arena, 32, 20);
  EXPECT_EQ(aa->int_data.size(), 2u);
  EXPECT_EQ(aa->int_data[1].ToUint64(), 10u);
  EXPECT_EQ(aa->int_data[2].ToUint64(), 20u);
}

TEST(AssocMethods, LiteralInitWithDefault) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 99);
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_TRUE(aa->has_default);
  EXPECT_EQ(aa->default_value.ToUint64(), 99u);
}

TEST(AssocMethods, LiteralInitStringKeys) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["Peter"] = MakeLogic4VecVal(f.arena, 32, 20);
  aa->str_data["Paul"] = MakeLogic4VecVal(f.arena, 32, 22);
  aa->str_data["Mary"] = MakeLogic4VecVal(f.arena, 32, 23);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, static_cast<uint64_t>(-1));
  EXPECT_EQ(aa->str_data.size(), 3u);
  EXPECT_EQ(aa->str_data["Peter"].ToUint64(), 20u);
  EXPECT_TRUE(aa->has_default);
}

}
