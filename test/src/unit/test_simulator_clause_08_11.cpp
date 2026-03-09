#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, ThisPushPop) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
  f.ctx.PushThis(obj);
  EXPECT_EQ(f.ctx.CurrentThis(), obj);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
}

TEST(ClassSim, NestedThisScoping) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [h1, obj1] = MakeObj(f, type);
  auto [h2, obj2] = MakeObj(f, type);

  f.ctx.PushThis(obj1);
  EXPECT_EQ(f.ctx.CurrentThis(), obj1);
  f.ctx.PushThis(obj2);
  EXPECT_EQ(f.ctx.CurrentThis(), obj2);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), obj1);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
}

TEST(ClassSim, ThisPropertyAccess) {
  SimFixture f;
  auto* type = MakeClassType(f, "Demo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 99));
  f.ctx.PushThis(obj);

  auto* current = f.ctx.CurrentThis();
  ASSERT_NE(current, nullptr);
  auto val = current->GetProperty("x", f.arena);
  EXPECT_EQ(val.ToUint64(), 99u);

  f.ctx.PopThis();
}

TEST(ClassSim, ThisCorrectObjectInNestedCalls) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"val"});
  auto [h1, obj1] = MakeObj(f, type);
  auto [h2, obj2] = MakeObj(f, type);

  obj1->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 10));
  obj2->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 20));

  f.ctx.PushThis(obj1);
  EXPECT_EQ(f.ctx.CurrentThis()->GetProperty("val", f.arena).ToUint64(), 10u);

  f.ctx.PushThis(obj2);
  EXPECT_EQ(f.ctx.CurrentThis()->GetProperty("val", f.arena).ToUint64(), 20u);

  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis()->GetProperty("val", f.arena).ToUint64(), 10u);

  f.ctx.PopThis();
}

}  // namespace
