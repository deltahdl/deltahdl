
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, HandleCopiedNotObjectContents) {
  SimFixture f;
  auto* type = MakeClassType(f, "Data", {"value"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 10));

  // Simulate passing the handle as an argument (copy the handle value).
  uint64_t arg_handle = handle;

  // Modify property through the copied handle.
  auto* arg_obj = f.ctx.GetClassObject(arg_handle);
  arg_obj->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 99));

  // The original sees the change because the handle was copied, not the
  // object contents.
  EXPECT_EQ(obj->GetProperty("value", f.arena).ToUint64(), 99u);
}

TEST(ClassSim, ClassContainsBothPropertiesAndMethods) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"command", "status"});

  auto* task_method = f.arena.Create<ModuleItem>();
  task_method->kind = ModuleItemKind::kTaskDecl;
  task_method->name = "clean";
  type->methods["clean"] = task_method;

  auto* func_method = f.arena.Create<ModuleItem>();
  func_method->kind = ModuleItemKind::kFunctionDecl;
  func_method->name = "current_status";
  type->methods["current_status"] = func_method;

  auto [handle, obj] = MakeObj(f, type);

  // Properties are accessible.
  obj->SetProperty("command", MakeLogic4VecVal(f.arena, 32, 7));
  EXPECT_EQ(obj->GetProperty("command", f.arena).ToUint64(), 7u);

  // Both function and task methods are resolvable.
  EXPECT_NE(obj->ResolveMethod("clean"), nullptr);
  EXPECT_NE(obj->ResolveMethod("current_status"), nullptr);
}

TEST(ClassSim, DeallocatedObjectBecomesInvalid) {
  SimFixture f;
  auto* type = MakeClassType(f, "Temp", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  ASSERT_NE(f.ctx.GetClassObject(handle), nullptr);

  f.ctx.DeallocateClassObject(handle);
  EXPECT_EQ(f.ctx.GetClassObject(handle), nullptr);
}

TEST(ClassSim, DeallocateNullHandleIsHarmless) {
  SimFixture f;
  f.ctx.DeallocateClassObject(kNullClassHandle);
  f.ctx.DeallocateClassObject(99999);
}

}  // namespace
