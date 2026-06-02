#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakRefGetIdNull) {
  EXPECT_EQ(WeakReference::GetId(kNullClassHandle), 0);
}

TEST(ClassSim, WeakRefGetIdNonzero) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_NE(WeakReference::GetId(handle), 0);
}

TEST(ClassSim, WeakRefGetIdDeterministic) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  auto id1 = WeakReference::GetId(handle);
  auto id2 = WeakReference::GetId(handle);
  EXPECT_EQ(id1, id2);
}

TEST(ClassSim, WeakRefGetIdUnique) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [h1, o1] = MakeObj(f, type);
  auto [h2, o2] = MakeObj(f, type);
  EXPECT_NE(WeakReference::GetId(h1), WeakReference::GetId(h2));
}

TEST(ClassSim, WeakRefGetIdUniqueAcrossTypes) {
  SimFixture f;
  auto* type_a = MakeClassType(f, "alpha", {"a"});
  auto* type_b = MakeClassType(f, "beta", {"b"});
  auto [h1, o1] = MakeObj(f, type_a);
  auto [h2, o2] = MakeObj(f, type_b);
  EXPECT_NE(WeakReference::GetId(h1), WeakReference::GetId(h2));
}

TEST(ClassSim, WeakRefGetIdSameAcrossInheritanceTree) {
  SimFixture f;
  auto* parent = MakeClassType(f, "parent", {"x"});
  auto* child = f.arena.Create<ClassTypeInfo>();
  child->name = "child";
  child->parent = parent;
  child->properties.push_back({"y", 32, false});
  f.ctx.RegisterClassType("child", child);

  auto [handle, obj] = MakeObj(f, child);
  auto id_via_child = WeakReference::GetId(handle);
  auto id_via_parent = WeakReference::GetId(handle);
  EXPECT_EQ(id_via_child, id_via_parent);
}

// §8.30.5: the id is independent of where the queried handle sits in the
// inheritance tree. Drive the production static-call path end to end: one
// handle is base-typed and one is derived-typed, but both refer to the same
// object, so get_id() through the two distinct specializations must agree (and
// be nonzero for a live object). This exercises the runtime dispatch that maps
// weak_reference#(T)::get_id(obj) onto the production id computation.
TEST(ClassSim, WeakRefGetIdStaticCallSameAcrossSpecializations) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class obj;\n"
      "  int x;\n"
      "endclass\n"
      "class ex_obj extends obj;\n"
      "  int y;\n"
      "endclass\n"
      "module m;\n"
      "  obj base_ref;\n"
      "  ex_obj derived_ref;\n"
      "  longint id_base;\n"
      "  longint id_derived;\n"
      "  initial begin\n"
      "    derived_ref = new();\n"
      "    base_ref = derived_ref;\n"
      "    id_base = weak_reference#(obj)::get_id(base_ref);\n"
      "    id_derived = weak_reference#(ex_obj)::get_id(derived_ref);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* id_base = f.ctx.FindVariable("id_base");
  auto* id_derived = f.ctx.FindVariable("id_derived");
  ASSERT_NE(id_base, nullptr);
  ASSERT_NE(id_derived, nullptr);
  EXPECT_NE(id_base->value.ToUint64(), 0u);
  EXPECT_EQ(id_base->value.ToUint64(), id_derived->value.ToUint64());
}

}
