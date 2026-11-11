#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
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

TEST(ClassSim, WeakRefGetIdStaticCallNullReferentReturnsZero) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module m;\n"
                      "  obj h;\n"
                      "  longint id;\n"
                      "  initial begin\n"
                      "    h = null;\n"
                      "    id = weak_reference#(obj)::get_id(h);\n"
                      "  end\n"
                      "endmodule\n",
                      "id"),
            0u);
}

TEST(ClassSim, WeakRefGetIdStaticCallDistinctObjectsDistinctIds) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module m;\n"
                      "  obj a;\n"
                      "  obj b;\n"
                      "  longint ida;\n"
                      "  longint idb;\n"
                      "  bit distinct_nonzero;\n"
                      "  initial begin\n"
                      "    a = new();\n"
                      "    b = new();\n"
                      "    ida = weak_reference#(obj)::get_id(a);\n"
                      "    idb = weak_reference#(obj)::get_id(b);\n"
                      "    distinct_nonzero =\n"
                      "        (ida != idb) && (ida != 0) && (idb != 0);\n"
                      "  end\n"
                      "endmodule\n",
                      "distinct_nonzero"),
            1u);
}

TEST(ClassSim, WeakRefGetIdDerivedHandleSameThroughBaseAndDerivedSpec) {
  EXPECT_EQ(
      RunAndGet("class obj;\n"
                "  int x;\n"
                "endclass\n"
                "class ex_obj extends obj;\n"
                "  int y;\n"
                "endclass\n"
                "module m;\n"
                "  ex_obj my_obj;\n"
                "  bit same_nonzero;\n"
                "  initial begin\n"
                "    my_obj = new();\n"
                "    same_nonzero =\n"
                "        (weak_reference#(obj)::get_id(my_obj) ==\n"
                "         weak_reference#(ex_obj)::get_id(my_obj)) &&\n"
                "        (weak_reference#(ex_obj)::get_id(my_obj) != 0);\n"
                "  end\n"
                "endmodule\n",
                "same_nonzero"),
      1u);
}

TEST(ClassSim, WeakRefGetIdIsSixtyFourBitsAndIndexesAnAssociativeArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class B; int x = 7; endclass\n"
      "module m;\n"
      "  B b;\n"
      "  int aa[longint];\n"
      "  int r1, r3;\n"
      "  initial begin\n"
      "    b = new;\n"
      "    r1 = $bits(weak_reference #(B)::get_id(b));\n"
      "    aa[weak_reference #(B)::get_id(b)] = 1;\n"
      "    r3 = aa.exists(weak_reference #(B)::get_id(b));\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 64u}, {"r3", 1u}});
}

TEST(ClassSim, DISABLED_WeakRefGetIdComparesAsSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class B; int x = 7; endclass\n"
      "module m;\n"
      "  B b;\n"
      "  int r2;\n"
      "  initial begin\n"
      "    b = new;\n"
      "    r2 = (weak_reference #(B)::get_id(b) > -1);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r2", 1u}});
}

}  // namespace
