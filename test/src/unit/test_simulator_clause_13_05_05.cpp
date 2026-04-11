#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ArgumentBindingSim, VoidFunctionNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void set_x;\n"
      "    x = 8'd66;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

TEST(ArgumentBindingSim, TaskCallNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd88;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(ArgumentBindingSim, TaskAllDefaultsNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task set_x(int v = 42);\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 32'd0;\n"
      "    set_x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(ArgumentBindingSim, VoidFunctionAllDefaultsNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void set_x(int v = 99);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 32'd0;\n"
      "    set_x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 99u}});
}

TEST(ArgumentBindingSim, TaskMultipleDefaultsNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task compute(int a = 3, int b = 7);\n"
      "    x = a + b;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 32'd0;\n"
      "    compute;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 10u}});
}

}  // namespace
