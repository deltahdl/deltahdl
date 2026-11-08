#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

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

TEST(ClassSim, WeakRefE2eGetQueriesReferentBuiltInDeclInit) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static obj strong_obj = new();\n"
                      "    static weak_reference #(obj) wr = new(strong_obj);\n"
                      "    result = (wr.get() == strong_obj);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

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
