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

TEST(ClassSim, HandleNullAssignment) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(handle), obj);

  uint64_t null_handle = kNullClassHandle;
  EXPECT_EQ(f.ctx.GetClassObject(null_handle), nullptr);
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

// §8.4: assignment of a class object copies the handle, so two variables that
// were assigned from the same allocated object refer to that one object and
// compare equal. Exercised end to end (elaborate/lower/run) rather than from a
// hand-built handle value: 'new' produces the object, the assignment aliases
// the second handle, and the listed '==' / '===' operators observe the alias.
TEST(ClassSim, AssignedHandlesAliasSameObjectCompareEqual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  logic eq;\n"
      "  logic ceq;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new;\n"
      "    b = a;\n"
      "    eq = (a == b);\n"
      "    ceq = (a === b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* eq = f.ctx.FindVariable("eq");
  auto* ceq = f.ctx.FindVariable("ceq");
  ASSERT_NE(eq, nullptr);
  ASSERT_NE(ceq, nullptr);
  EXPECT_EQ(eq->value.ToUint64(), 1u);
  EXPECT_EQ(ceq->value.ToUint64(), 1u);
}

// §8.4: distinct objects created by separate 'new' calls have distinct handles,
// so handles pointing at different objects compare unequal. Built from real
// source syntax and run through the full pipeline so the '==' / '!=' operators
// act on handles the allocator actually produced.
TEST(ClassSim, DistinctObjectsCompareUnequal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  logic eq;\n"
      "  logic neq;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    eq = (a == b);\n"
      "    neq = (a != b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* eq = f.ctx.FindVariable("eq");
  auto* neq = f.ctx.FindVariable("neq");
  ASSERT_NE(eq, nullptr);
  ASSERT_NE(neq, nullptr);
  EXPECT_EQ(eq->value.ToUint64(), 0u);
  EXPECT_EQ(neq->value.ToUint64(), 1u);
}

// §8.4: the conditional operator is one of the operators valid on object
// handles. Built end to end from 11.4.11's real ternary syntax -- two distinct
// objects are allocated and each branch is selected in turn, so the result
// handle aliases the object the condition chose, observed with '=='.
TEST(ClassSim, ConditionalOperatorSelectsHandleAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  logic picks_a;\n"
      "  logic picks_b;\n"
      "  initial begin\n"
      "    C a, b, ta, tb;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    ta = 1'b1 ? a : b;\n"
      "    tb = 1'b0 ? a : b;\n"
      "    picks_a = (ta == a);\n"
      "    picks_b = (tb == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* pa = f.ctx.FindVariable("picks_a");
  auto* pb = f.ctx.FindVariable("picks_b");
  ASSERT_NE(pa, nullptr);
  ASSERT_NE(pb, nullptr);
  EXPECT_EQ(pa->value.ToUint64(), 1u);
  EXPECT_EQ(pb->value.ToUint64(), 1u);
}

// §8.4: assignment of a class object whose type is assignment compatible with
// the target is valid. The compatible source is a derived-class handle built
// from 6.22.3's real 'extends' inheritance; after assigning it into a base
// handle the two handles alias the one object, observed with '=='.
TEST(ClassSim, CompatibleDerivedHandleAssignmentAliasesAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base; endclass\n"
      "class Child extends Base; endclass\n"
      "module m;\n"
      "  logic aliased;\n"
      "  initial begin\n"
      "    Base bh;\n"
      "    Child ch;\n"
      "    ch = new;\n"
      "    bh = ch;\n"
      "    aliased = (bh == ch);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* aliased = f.ctx.FindVariable("aliased");
  ASSERT_NE(aliased, nullptr);
  EXPECT_EQ(aliased->value.ToUint64(), 1u);
}

// §8.4: assignment of null is a valid operation on an object handle. After an
// object is allocated and null is then assigned over it, comparing the handle
// with null yields true -- observed end to end rather than from a hand-set
// handle value.
TEST(ClassSim, NullAssignmentClearsHandleAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  logic is_null;\n"
      "  initial begin\n"
      "    C h;\n"
      "    h = new;\n"
      "    h = null;\n"
      "    is_null = (h == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("is_null");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

TEST(ClassSim, UninitializedHandleDetectableAsNull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C h;\n"
      "  logic is_null;\n"
      "  initial is_null = (h == null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("is_null");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
