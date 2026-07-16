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

// §8.30.5: get_id() of a null referent shall return 0 -- the reject path that
// sits opposite the nonzero live-object path. The synthetic call above proves
// the leaf function returns 0 for a null handle; this drives the same rule
// through the production static-call dispatch instead. A real class handle is
// declared and assigned null (§8.16), then passed to
// weak_reference#(obj)::get_id(h); the dispatch must evaluate the null handle
// to 0, route it to the id computation, and yield 0. This is the only
// full-pipeline observation of the null branch.
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

// §8.30.5: the id shall be unique with respect to all other objects for the
// lifetime of each instance. The synthetic uniqueness tests compare ids from
// hand-built objects; this observes the rule end to end. Two distinct objects
// are created with real new() (§8.25 constructs the weak_reference
// specialization used to name the call) and queried through the production
// static-call dispatch. Both ids must be nonzero and must differ, so the
// aggregated flag is 1.
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

// §8.30.5: the clause's own worked example -- a single object handle queried
// through a base-class specialization and a derived-class specialization of
// get_id yields the identical, nonzero id. One derived-typed handle (ex_obj) is
// passed to BOTH weak_reference#(obj)::get_id and weak_reference#(ex_obj)::
// get_id; the base specialization accepts the derived handle by assignment
// compatibility (§8.16), and both static calls name their specialization with
// real weak_reference#(T) syntax (§8.25). The two ids are compared inside a
// single equality expression -- get_id in an operand position -- so the
// referent identity is shown to be independent of the handle's location in the
// inheritance tree. Built from real new() source and driven end to end. This is
// distinct from the two-variable SameAcrossSpecializations test above: here the
// same derived handle flows into a base-parameterized get_id.
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

}  // namespace
