#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, AllocateNewObject) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"header", "payload"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_NE(handle, kNullClassHandle);
  EXPECT_EQ(obj->type, type);
  EXPECT_EQ(obj->GetProperty("header", f.arena).ToUint64(), 0u);
}

TEST(ClassSim, NewReturnsUniqueHandles) {
  SimFixture f;
  auto* type = MakeClassType(f, "MyClass", {"x"});
  auto [h1, _1] = MakeObj(f, type);
  auto [h2, _2] = MakeObj(f, type);

  EXPECT_NE(h1, h2);
}

TEST(ClassSim, HandleToObjectLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"val"});
  auto [handle, obj] = MakeObj(f, type);

  auto* retrieved = f.ctx.GetClassObject(handle);
  EXPECT_EQ(retrieved, obj);
}

TEST(ClassSim, NullHandleIsZero) { EXPECT_EQ(kNullClassHandle, 0u); }

TEST(ClassSim, GetClassObjectNullReturnsNullptr) {
  SimFixture f;
  auto* obj = f.ctx.GetClassObject(kNullClassHandle);
  EXPECT_EQ(obj, nullptr);
}

TEST(ClassSim, GetClassObjectInvalidReturnsNullptr) {
  SimFixture f;
  auto* obj = f.ctx.GetClassObject(99999);
  EXPECT_EQ(obj, nullptr);
}

TEST(ClassSim, ClassTypeRegistryLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "Registry", {"x"});

  auto* found = f.ctx.FindClassType("Registry");
  EXPECT_EQ(found, type);

  auto* notfound = f.ctx.FindClassType("Nonexistent");
  EXPECT_EQ(notfound, nullptr);
}

TEST(ClassSim, MultipleObjectsSameType) {
  SimFixture f;
  auto* type = MakeClassType(f, "Widget", {"value"});

  auto [h1, o1] = MakeObj(f, type);
  auto [h2, o2] = MakeObj(f, type);

  o1->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 100));
  o2->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 200));

  EXPECT_EQ(o1->GetProperty("value", f.arena).ToUint64(), 100u);
  EXPECT_EQ(o2->GetProperty("value", f.arena).ToUint64(), 200u);
}

TEST(ClassSim, TwoHandlesSameObjectShareState) {
  SimFixture f;
  auto* type = MakeClassType(f, "Shared", {"val"});
  auto [handle, obj] = MakeObj(f, type);

  // Simulate assigning the handle to another variable.
  uint64_t handle2 = handle;

  // Both handles resolve to the exact same object.
  auto* obj_via_h1 = f.ctx.GetClassObject(handle);
  auto* obj_via_h2 = f.ctx.GetClassObject(handle2);
  EXPECT_EQ(obj_via_h1, obj_via_h2);

  // Mutation through one handle is visible through the other.
  obj_via_h1->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 42));
  EXPECT_EQ(obj_via_h2->GetProperty("val", f.arena).ToUint64(), 42u);
}

TEST(ClassSim, HandleNullAssignment) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(handle), obj);

  uint64_t null_handle = kNullClassHandle;
  EXPECT_EQ(f.ctx.GetClassObject(null_handle), nullptr);
}

TEST(ClassSim, HandleEqualitySameHandleReturnsOne) {
  SimFixture f;
  auto h = MakeLogic4VecVal(f.arena, 64, 5);
  auto result = EvalBinaryOp(TokenKind::kEqEq, h, h, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ClassSim, HandleEqualityDifferentHandlesReturnsZero) {
  SimFixture f;
  auto h1 = MakeLogic4VecVal(f.arena, 64, 5);
  auto h2 = MakeLogic4VecVal(f.arena, 64, 6);
  auto result = EvalBinaryOp(TokenKind::kEqEq, h1, h2, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ClassSim, HandleInequalityDifferentHandlesReturnsOne) {
  SimFixture f;
  auto h1 = MakeLogic4VecVal(f.arena, 64, 5);
  auto h2 = MakeLogic4VecVal(f.arena, 64, 6);
  auto result = EvalBinaryOp(TokenKind::kBangEq, h1, h2, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ClassSim, HandleCaseEqualitySameHandleReturnsOne) {
  SimFixture f;
  auto h = MakeLogic4VecVal(f.arena, 64, 5);
  auto result = EvalBinaryOp(TokenKind::kEqEqEq, h, h, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ClassSim, HandleCaseInequalityDifferentHandlesReturnsOne) {
  SimFixture f;
  auto h1 = MakeLogic4VecVal(f.arena, 64, 5);
  auto h2 = MakeLogic4VecVal(f.arena, 64, 6);
  auto result = EvalBinaryOp(TokenKind::kBangEqEq, h1, h2, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ClassSim, HandleEqualityBothNullReturnsOne) {
  SimFixture f;
  auto null1 = MakeLogic4VecVal(f.arena, 64, kNullClassHandle);
  auto null2 = MakeLogic4VecVal(f.arena, 64, kNullClassHandle);
  auto result = EvalBinaryOp(TokenKind::kEqEq, null1, null2, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ClassSim, HandleNotEqualToNullReturnsOne) {
  SimFixture f;
  auto* type = MakeClassType(f, "T", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  auto h = MakeLogic4VecVal(f.arena, 64, handle);
  auto null_h = MakeLogic4VecVal(f.arena, 64, kNullClassHandle);
  auto result = EvalBinaryOp(TokenKind::kBangEq, h, null_h, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ClassSim, CaseEqualitySameSemanticsAsEquality) {
  SimFixture f;
  auto h1 = MakeLogic4VecVal(f.arena, 64, 7);
  auto h2 = MakeLogic4VecVal(f.arena, 64, 7);
  auto h3 = MakeLogic4VecVal(f.arena, 64, 8);
  auto eq = EvalBinaryOp(TokenKind::kEqEq, h1, h2, f.arena);
  auto ceq = EvalBinaryOp(TokenKind::kEqEqEq, h1, h2, f.arena);
  EXPECT_EQ(eq.ToUint64(), ceq.ToUint64());
  auto neq = EvalBinaryOp(TokenKind::kBangEq, h1, h3, f.arena);
  auto cneq = EvalBinaryOp(TokenKind::kBangEqEq, h1, h3, f.arena);
  EXPECT_EQ(neq.ToUint64(), cneq.ToUint64());
}

TEST(ClassSim, IsAReturnsTrueForSameType) {
  SimFixture f;
  auto* type = MakeClassType(f, "Base", {"x"});
  EXPECT_TRUE(type->IsA(type));
}

TEST(ClassSim, IsAReturnsTrueForParentType) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* child = MakeClassType(f, "Child", {"y"});
  child->parent = base;
  EXPECT_TRUE(child->IsA(base));
  EXPECT_FALSE(base->IsA(child));
}

TEST(ClassSim, IsAReturnsFalseForUnrelatedType) {
  SimFixture f;
  auto* a = MakeClassType(f, "A", {"x"});
  auto* b = MakeClassType(f, "B", {"y"});
  EXPECT_FALSE(a->IsA(b));
  EXPECT_FALSE(b->IsA(a));
}

}  // namespace
