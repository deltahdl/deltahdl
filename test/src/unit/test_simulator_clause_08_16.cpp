#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, CastSubclassToSuperclassAlwaysLegal) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {"i"});
  auto* derived = MakeClassType(f, "LinkedPacket", {"j"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  EXPECT_TRUE(obj->type->IsA(base));
}

TEST(ClassSim, CastSuperclassToSubclassIllegal) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, base);
  EXPECT_FALSE(obj->type->IsA(derived));
}

TEST(ClassSim, CastSucceedsWhenObjectIsDerived) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* derived = MakeClassType(f, "Derived", {"y"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  EXPECT_TRUE(obj->type->IsA(derived));
  EXPECT_TRUE(obj->type->IsA(base));
}

TEST(ClassSim, CastFailsUnrelatedTypes) {
  SimFixture f;
  auto* type_a = MakeClassType(f, "TypeA", {});
  auto* type_b = MakeClassType(f, "TypeB", {});

  auto [handle, obj] = MakeObj(f, type_a);
  EXPECT_FALSE(obj->type->IsA(type_b));
}

TEST(ClassSim, CastNullHandleIsZero) {
  SimFixture f;
  EXPECT_EQ(f.ctx.GetClassObject(kNullClassHandle), nullptr);
}

TEST(ClassSim, CastDeepHierarchySucceeds) {
  SimFixture f;
  auto* grand = MakeClassType(f, "Grand", {});
  auto* mid = MakeClassType(f, "Mid", {});
  mid->parent = grand;
  auto* leaf = MakeClassType(f, "Leaf", {});
  leaf->parent = mid;

  auto [handle, obj] = MakeObj(f, leaf);
  EXPECT_TRUE(obj->type->IsA(grand));
  EXPECT_TRUE(obj->type->IsA(mid));

  auto [h2, obj2] = MakeObj(f, grand);
  EXPECT_FALSE(obj2->type->IsA(leaf));
}

TEST(ClassSim, E2eCastFunctionReturnsOneOnSuccess) {
  EXPECT_EQ(RunAndGet(
      "class Base; int x; endclass\n"
      "class Derived extends Base; int y; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    b = d;\n"
      "    result = $cast(d, b);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(ClassSim, E2eCastFunctionReturnsZeroOnFailure) {
  EXPECT_EQ(RunAndGet(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    b = new;\n"
      "    result = $cast(d, b);\n"
      "  end\n"
      "endmodule\n", "result"), 0u);
}

TEST(ClassSim, E2eCastTaskFormFailsWithError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    b = new;\n"
      "    $cast(d, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ClassSim, E2eCastNullSucceeds) {
  EXPECT_EQ(RunAndGet(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    result = $cast(d, null);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(ClassSim, E2eCastNullAssignsNull) {
  EXPECT_EQ(RunAndGet(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    $cast(d, null);\n"
      "    result = (d == null);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(ClassSim, E2eUpcastAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base; int x; endclass\n"
      "class Derived extends Base; int y; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    Base b;\n"
      "    d = new;\n"
      "    b = d;\n"
      "    result = (b != null);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 1u}});
}

TEST(ClassSim, E2eCastDeepHierarchyDowncast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Grand; endclass\n"
      "class Mid extends Grand; endclass\n"
      "class Leaf extends Mid; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Grand g;\n"
      "    Leaf l;\n"
      "    l = new;\n"
      "    g = l;\n"
      "    result = $cast(l, g);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 1u}});
}

TEST(ClassSim, E2eCastDeepHierarchyDowncastFails) {
  EXPECT_EQ(RunAndGet(
      "class Grand; endclass\n"
      "class Mid extends Grand; endclass\n"
      "class Leaf extends Mid; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Grand g;\n"
      "    Leaf l;\n"
      "    g = new;\n"
      "    result = $cast(l, g);\n"
      "  end\n"
      "endmodule\n", "result"), 0u);
}

TEST(ClassSim, E2eCastFailsIncompatibleTypesEvenIfNull) {
  EXPECT_EQ(RunAndGet(
      "class A; endclass\n"
      "class B; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    A a;\n"
      "    B b;\n"
      "    result = $cast(a, b);\n"
      "  end\n"
      "endmodule\n", "result"), 0u);
}

}  // namespace
