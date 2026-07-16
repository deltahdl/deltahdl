#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// --- §8.30.3 get() observed through the full pipeline ------------------------
//
// §8.30.3 governs the weak_reference get() method: while the reference has not
// been cleared, get() returns the referent value used to initialize it
// (SHALL#1); otherwise it returns null (SHALL#2). Whether the reference has
// been cleared, and what value was recorded, both depend on how the input was
// produced -- the referent comes from a real §8.30.2 new(referent) and the
// cleared state from clearing that reference. The tests below build those
// inputs from source and drive parse/elaborate/lower/run, observing the
// production get() path rather than a hand-built wrapper.

// §8.30.3 SHALL#1: with the reference intact, get() returns the referent handed
// to the constructor. Built via a procedural new(referent); the query is the
// production get() path and its result compared to the original strong handle.
TEST(ClassSim, WeakRefE2eGetQueriesReferentNotCleared) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    wr = new(strong_obj);\n"
                      "    result = (wr.get() == strong_obj);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.3 SHALL#1, declaration-initializer production form: the weak reference
// is built in its own declaration (weak_reference#(T) wr = new(referent)) -- a
// distinct §8.30.2 syntactic position from the procedural assignment above.
// get() still returns the referent recorded at construction. Driven end to end.
TEST(ClassSim, WeakRefE2eGetQueriesReferentBuiltInDeclInit) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj = new();\n"
                      "    weak_reference #(obj) wr = new(strong_obj);\n"
                      "    result = (wr.get() == strong_obj);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.3 SHALL#1, "referent value used to initialize": the handle get()
// returns is the actual referent, so a field written on the object before the
// query is visible when read back through get()'s result. Built from real
// new(referent) source and driven end to end.
TEST(ClassSim, WeakRefE2eGetResultIsUsableReferent) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    obj got;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    strong_obj.x = 42;\n"
                      "    wr = new(strong_obj);\n"
                      "    got = wr.get();\n"
                      "    result = got.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

// §8.30.3 SHALL#2: once the reference has been cleared, get() returns null
// instead of the original referent. The reference is built from real
// new(referent) source and then cleared, so this drives the production
// cleared-then-query path -- the branch §8.30.2's recording tests never reach.
TEST(ClassSim, WeakRefE2eGetReturnsNullAfterCleared) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    wr = new(strong_obj);\n"
                      "    wr.clear();\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.3: get() used in an event-control expression to detect that the
// reference has been cleared. Once the reference is cleared, get() evaluates to
// null inside a wait condition, so the process unblocks and proceeds --
// observed by the statement past the wait taking effect. Built entirely from
// source.
TEST(ClassSim, WeakRefE2eGetInWaitDetectsCleared) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    wr = new(strong_obj);\n"
                      "    wr.clear();\n"
                      "    wait (wr.get() == null);\n"
                      "    result = 1;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.3 SHALL#1 with a null initializer: a reference constructed over a null
// referent has not been cleared, so get() returns the value used to initialize
// it -- null. Built from real new(null) source.
TEST(ClassSim, WeakRefE2eGetNullInitQueriesNull) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    weak_reference #(obj) wr;\n"
                      "    wr = new(null);\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.30.3 SHALL#2, cleared by the memory management system (§8.29): after the
// referent is reclaimed by garbage collection, get() returns null. Garbage
// collection cannot be triggered from SystemVerilog source, so this drives the
// production reclamation path directly and observes the production get().
TEST(ClassSim, WeakRefGetReturnsNullAfterGc) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto wr_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);
  EXPECT_EQ(wr->Get(), handle);

  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();
  EXPECT_EQ(wr->Get(), kNullClassHandle);
}

// §8.30.3 SHALL#1 under garbage collection: when the collector runs but the
// referent is still strongly reachable, the reference is not cleared, so get()
// keeps returning the referent used to initialize it. A live class-typed
// variable holding the object keeps it in the reachable set, so the production
// collector leaves the weak reference intact.
TEST(ClassSim, WeakRefGetReturnsReferentWhenGcSparesReachable) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto* strong = f.ctx.CreateVariable("strong", 64);
  f.ctx.SetVariableClassType("strong", "obj");
  strong->value = MakeLogic4VecVal(f.arena, 64, handle);

  auto wr_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);

  f.ctx.CollectGarbage();
  EXPECT_EQ(wr->Get(), handle);
  auto* retrieved = f.ctx.GetClassObject(wr->Get());
  ASSERT_NE(retrieved, nullptr);
  EXPECT_EQ(retrieved, obj);
}

}  // namespace
