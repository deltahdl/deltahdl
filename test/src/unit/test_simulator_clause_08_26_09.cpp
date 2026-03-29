#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InterfaceClassRandomizeSim, RandomizeOnInterfaceHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  constraint c { x >= 1; x <= 100; }\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    IC iref = obj;\n"
      "    void'(iref.randomize());\n"
      "    result = obj.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.has_errors);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  uint64_t val = var->value.ToUint64();
  EXPECT_GE(val, 1u);
  EXPECT_LE(val, 100u);
}

TEST(InterfaceClassRandomizeSim, RandomizeReturnValue) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  constraint c { x > 0; x < 10; }\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    IC iref = obj;\n"
      "    result = iref.randomize();\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(InterfaceClassPrePostRandomizeSim, PreRandomizeCalledBeforeRandomize) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  int pre_called;\n"
      "  constraint c { x > 0; x < 10; }\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "  function void pre_randomize();\n"
      "    pre_called = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    void'(obj.randomize());\n"
      "    result = obj.pre_called;\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(InterfaceClassPrePostRandomizeSim, PostRandomizeCalledAfterRandomize) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  int post_called;\n"
      "  constraint c { x > 0; x < 10; }\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "  function void post_randomize();\n"
      "    post_called = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    void'(obj.randomize());\n"
      "    result = obj.post_called;\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(InterfaceClassPrePostRandomizeSim, PreRandomizeViaInterfaceHandle) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  int pre_called;\n"
      "  constraint c { x > 0; x < 10; }\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "  function void pre_randomize();\n"
      "    pre_called = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    IC iref = obj;\n"
      "    void'(iref.randomize());\n"
      "    result = obj.pre_called;\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(InterfaceClassPrePostRandomizeSim, PostRandomizeViaInterfaceHandle) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  int post_called;\n"
      "  constraint c { x > 0; x < 10; }\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "  function void post_randomize();\n"
      "    post_called = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    IC iref = obj;\n"
      "    void'(iref.randomize());\n"
      "    result = obj.post_called;\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

}  // namespace
