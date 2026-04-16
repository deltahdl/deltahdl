#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- R14: Hierarchical name can be read in an expression ---

TEST(HierarchicalNameSimulation, ReadChildInstanceVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] val;\n"
      "  initial val = 8'd42;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = c1.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

// --- R14: Hierarchical name can be written in an assignment ---

TEST(HierarchicalNameSimulation, WriteChildInstanceVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] val;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  initial begin\n"
      "    c1.val = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("c1.val");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

// --- R10/R14: Complete path from top-level, multi-level read ---

TEST(HierarchicalNameSimulation, MultiLevelHierarchicalRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  logic [7:0] data;\n"
      "  initial data = 8'd77;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = m1.l1.data;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

// --- R11: Relative downward referencing (first node at current level) ---

TEST(HierarchicalNameSimulation, RelativeDownwardReference) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] sig;\n"
      "  initial sig = 8'd55;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = c1.sig;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 55u);
}

// --- R14: Hierarchical name used in event expression (trigger) ---

TEST(HierarchicalNameSimulation, HierarchicalNameInEventExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic done;\n"
      "  initial begin\n"
      "    done = 0;\n"
      "    #10 done = 1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd0;\n"
      "    @(posedge c1.done);\n"
      "    result = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

}  // namespace
