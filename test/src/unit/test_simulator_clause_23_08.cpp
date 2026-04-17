#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Read via upward reference: a lower module reads a variable in its enclosing
// module using the enclosing module's name.

TEST(UpwardNameReferenceSimulation, UpwardReadReturnsEnclosingValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    #1;\n"
      "    r = parent.v;\n"
      "  end\n"
      "endmodule\n"
      "module parent;\n"
      "  integer v;\n"
      "  child c1();\n"
      "  initial v = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("c1.r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

// Write via upward reference: a lower module writes a variable in its
// enclosing module.

TEST(UpwardNameReferenceSimulation, UpwardWriteUpdatesEnclosingVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  initial parent.v = 99;\n"
      "endmodule\n"
      "module parent;\n"
      "  integer v;\n"
      "  child c1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

// LRM canonical example: module c writes b.i (upward) — both parent-b copies
// receive the write, while local "i = 1" only writes c's own i.

TEST(UpwardNameReferenceSimulation, CanonicalExampleUpwardWriteHitsEnclosing) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 1;\n"
      "    b.i = 9;\n"
      "  end\n"
      "endmodule\n"
      "module b;\n"
      "  integer i;\n"
      "  c b_c1();\n"
      "endmodule\n"
      "module a;\n"
      "  integer i;\n"
      "  b a_b1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* b_i = f.ctx.FindVariable("a_b1.i");
  ASSERT_NE(b_i, nullptr);
  EXPECT_EQ(b_i->value.ToUint64(), 9u);
  auto* c_i = f.ctx.FindVariable("a_b1.b_c1.i");
  ASSERT_NE(c_i, nullptr);
  EXPECT_EQ(c_i->value.ToUint64(), 1u);
}

// Upward reference into the design-element scope (top-level module) resolves.

TEST(UpwardNameReferenceSimulation, UpwardReferenceAcrossTwoLevels) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    #1;\n"
      "    r = top.v;\n"
      "  end\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  integer v;\n"
      "  mid m1();\n"
      "  initial v = 55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("m1.l1.r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 55u);
}

}  // namespace
