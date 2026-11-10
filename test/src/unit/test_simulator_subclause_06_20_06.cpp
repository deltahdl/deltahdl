#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConstConstantSim, AutomaticConstTakesRuntimeArgumentValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int result;\n"
                      "  function automatic int add_one(int a);\n"
                      "    const int c = a + 1;\n"
                      "    return c;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    result = add_one(41);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ConstConstantSim, AutomaticConstReevaluatedEachCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r1, r2;\n"
      "  function automatic int add_one(int a);\n"
      "    const int c = a + 1;\n"
      "    return c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r1 = add_one(10);\n"
      "    r2 = add_one(20);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 11u}, {"r2", 21u}});
}

TEST(ConstConstantSim, AutomaticTaskConstReevaluatedEachCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r1, r2;\n"
      "  task automatic triple(input int a, output int o);\n"
      "    const int c = a * 3;\n"
      "    o = c;\n"
      "  endtask\n"
      "  initial begin\n"
      "    triple(2, r1);\n"
      "    triple(5, r2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"r1", 6u}, {"r2", 15u}});
}

TEST(ConstConstantSim, ConstVarAutomaticInBlockTakesRuntimeValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    int a;\n"
                      "    a = 3;\n"
                      "    begin\n"
                      "      const var automatic int x = a + 1;\n"
                      "      result = x;\n"
                      "    end\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            4u);
}

TEST(ConstConstantSim, AutomaticConstInLoopBodyNewValueEachEntry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r1, r2, r3;\n"
      "  int r[4];\n"
      "  initial begin\n"
      "    for (int i = 1; i < 4; i++) begin\n"
      "      const automatic int c = i * 2;\n"
      "      r[i] = c;\n"
      "    end\n"
      "    r1 = r[1];\n"
      "    r2 = r[2];\n"
      "    r3 = r[3];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"r1", 2u}, {"r2", 4u}, {"r3", 6u}});
}

TEST(ConstConstantSim, AutomaticConstReadsModuleVariableAtEntry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int m, r1, r2;\n"
      "  initial begin\n"
      "    m = 7;\n"
      "    for (int i = 0; i < 2; i++) begin\n"
      "      const automatic int c = m;\n"
      "      if (i == 0) r1 = c; else r2 = c;\n"
      "      m = 9;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"r1", 7u}, {"r2", 9u}});
}

TEST(ConstConstantSim, ImplicitlyAutomaticConstInTaskBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r1, r2;\n"
      "  task automatic dec(input int a, output int o);\n"
      "    begin\n"
      "      const int c = a - 1;\n"
      "      o = c;\n"
      "    end\n"
      "  endtask\n"
      "  initial begin\n"
      "    dec(5, r1);\n"
      "    dec(10, r2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"r1", 4u}, {"r2", 9u}});
}

TEST(ConstConstantSim, ClassMethodConstTakesRuntimeValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C;\n"
      "    int base = 100;\n"
      "    function int add(int a);\n"
      "      const int c = a + base;\n"
      "      return c;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r1, r2;\n"
      "  C obj;\n"
      "  initial begin\n"
      "    obj = new;\n"
      "    r1 = obj.add(5);\n"
      "    obj.base = 200;\n"
      "    r2 = obj.add(7);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"r1", 105u}, {"r2", 207u}});
}

TEST(ConstConstantSim, AutomaticConstFromFunctionCallReevaluated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int count, r1, r2;\n"
      "  function int next();\n"
      "    count = count + 1;\n"
      "    return count;\n"
      "  endfunction\n"
      "  function automatic int take();\n"
      "    const int c = next();\n"
      "    return c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    r1 = take();\n"
      "    r2 = take();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 2u}});
}

TEST(ConstConstantSim, AutomaticTaskConstReadsModuleVariableWhenCalled) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int g = 5;\n"
      "  int x, y;\n"
      "  task automatic twice(output int r);\n"
      "    const int c = g * 2;\n"
      "    r = c;\n"
      "  endtask\n"
      "  initial begin\n"
      "    g = 7;\n"
      "    twice(x);\n"
      "    g = 9;\n"
      "    twice(y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"x", 14u}, {"y", 18u}});
}

TEST(ConstConstantSim, ConstInAutomaticModuleSubroutineIsAutomatic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module automatic t;\n"
      "  int r1, r2, r3, r4;\n"
      "  task inc(input int a, output int o);\n"
      "    const int c = a + 1;\n"
      "    o = c;\n"
      "  endtask\n"
      "  function int dbl(int a);\n"
      "    const int c = a * 2;\n"
      "    return c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    inc(3, r1);\n"
      "    inc(8, r2);\n"
      "    r3 = dbl(3);\n"
      "    r4 = dbl(8);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design,
                   {{"r1", 4u}, {"r2", 9u}, {"r3", 6u}, {"r4", 16u}});
}

TEST(ConstConstantSim, ConstInAutomaticProgramSubroutineIsAutomatic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "program automatic p;\n"
      "  int r1, r2, r3, r4;\n"
      "  task sub(input int a, output int o);\n"
      "    const int c = a - 2;\n"
      "    o = c;\n"
      "  endtask\n"
      "  function int tri3(int a);\n"
      "    const int c = a * 3;\n"
      "    return c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    sub(5, r1);\n"
      "    sub(11, r2);\n"
      "    r3 = tri3(4);\n"
      "    r4 = tri3(7);\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  p u();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design,
                   {{"u.r1", 3u}, {"u.r2", 9u}, {"u.r3", 12u}, {"u.r4", 21u}});
}

TEST(ConstConstantSim, ConstInAutomaticInterfaceSubroutineIsAutomatic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface automatic ifc;\n"
      "  task add5(input int a, output int o);\n"
      "    const int c = a + 5;\n"
      "    o = c;\n"
      "  endtask\n"
      "  function int sq(int a);\n"
      "    const int c = a * a;\n"
      "    return c;\n"
      "  endfunction\n"
      "endinterface\n"
      "module t;\n"
      "  int r1, r2, r3, r4;\n"
      "  ifc u();\n"
      "  initial begin\n"
      "    u.add5(1, r1);\n"
      "    u.add5(4, r2);\n"
      "    r3 = u.sq(3);\n"
      "    r4 = u.sq(6);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design,
                   {{"r1", 6u}, {"r2", 9u}, {"r3", 9u}, {"r4", 36u}});
}

TEST(ConstConstantSim, ConstInAutomaticPackageSubroutineIsAutomatic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package automatic p;\n"
      "  task sub3(input int a, output int o);\n"
      "    const int c = a - 3;\n"
      "    o = c;\n"
      "  endtask\n"
      "  function int add7(int a);\n"
      "    const int c = a + 7;\n"
      "    return c;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  int r1, r2, r3, r4;\n"
      "  initial begin\n"
      "    p::sub3(10, r1);\n"
      "    p::sub3(20, r2);\n"
      "    r3 = p::add7(2);\n"
      "    r4 = p::add7(30);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design,
                   {{"r1", 7u}, {"r2", 17u}, {"r3", 9u}, {"r4", 37u}});
}

TEST(ConstConstantSim, ExplicitlyAutomaticConstInStaticSubroutine) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r1, r2, r3, r4;\n"
      "  task inc(input int a, output int o);\n"
      "    const automatic int c = a + 1;\n"
      "    o = c;\n"
      "  endtask\n"
      "  function int add_ten(int a);\n"
      "    const automatic int c = a + 10;\n"
      "    return c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    inc(2, r1);\n"
      "    inc(6, r2);\n"
      "    r3 = add_ten(1);\n"
      "    r4 = add_ten(5);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design,
                   {{"r1", 3u}, {"r2", 7u}, {"r3", 11u}, {"r4", 15u}});
}

TEST(ConstConstantSim, MemberWrittenThroughAConstHandleReadsBack) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  int x;\n"
      "  function new(int v);\n"
      "    x = v;\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new(5);\n"
      "  initial begin\n"
      "    obj.x = 7;\n"
      "    $display(\"%0d\", obj.x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "7\n");
}

TEST(ConstConstantSim,
     DISABLED_StaticConstReadsAParameterThroughAHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module sub; parameter P = 9; endmodule\n"
                 "module t;\n"
                 "  sub u();\n"
                 "  if (1) begin : a\n"
                 "    if (1) begin : b localparam logic [3:0] LP = 4'd6; end\n"
                 "  end\n"
                 "  const int c = u.P;\n"
                 "  const logic [3:0] option = a.b.LP;\n"
                 "  initial #1 $display(\"%0d %0d\", c, option);\n"
                 "endmodule\n",
                 f),
      "9 6\n");
}

}  // namespace
