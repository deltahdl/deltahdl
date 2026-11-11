#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

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
      "    static C obj = new;\n"
      "    static IC iref = obj;\n"
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
  EXPECT_EQ(RunAndGet("interface class IC;\n"
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
                      "    static C obj = new;\n"
                      "    static IC iref = obj;\n"
                      "    result = iref.randomize();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassRandomizeSim, InlineConstraintViaInterfaceHandleRandomizes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  constraint c { x >= 1; x <= 50; }\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    static IC iref = obj;\n"
      "    void'(iref.randomize() with { });\n"
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
  EXPECT_LE(val, 50u);
}

TEST(InterfaceClassPrePostRandomizeSim, PreRandomizeViaInterfaceHandle) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
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
                      "    static C obj = new;\n"
                      "    static IC iref = obj;\n"
                      "    void'(iref.randomize());\n"
                      "    result = obj.pre_called;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassPrePostRandomizeSim, PostRandomizeViaInterfaceHandle) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
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
                      "    static C obj = new;\n"
                      "    static IC iref = obj;\n"
                      "    void'(iref.randomize());\n"
                      "    result = obj.post_called;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassRandomizeSim,
     RandomizeAndInlineConstraintsThroughAnInterfaceHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class IR; pure virtual function int get(); endclass\n"
      "interface class IR2; pure virtual function int get2(); endclass\n"
      "class CR implements IR, IR2;\n"
      "  rand int v;\n"
      "  int pre, post;\n"
      "  constraint c { v inside {[1:5]}; }\n"
      "  virtual function int get(); return v; endfunction\n"
      "  virtual function int get2(); return pre * 10 + post; endfunction\n"
      "  function void pre_randomize(); pre = pre + 1; endfunction\n"
      "  function void post_randomize(); post = post + 1; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int r1, r2, r3, r4, r5;\n"
      "  IR ih;\n"
      "  IR2 i2;\n"
      "  int lim = 3;\n"
      "  initial begin\n"
      "    CR c;\n"
      "    c = new;\n"
      "    ih = c;\n"
      "    i2 = c;\n"
      "    r1 = ih.randomize();\n"
      "    r2 = (ih.get() >= 1 && ih.get() <= 5);\n"
      "    r3 = ih.randomize() with { lim > 2; };\n"
      "    r4 = i2.get2();\n"
      "    r5 = ih.randomize() with { lim > 5; };\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design, {{"r1", 1u}, {"r2", 1u}, {"r3", 1u}, {"r4", 22u}, {"r5", 0u}});
}

}  // namespace
