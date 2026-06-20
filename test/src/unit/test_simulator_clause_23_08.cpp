#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(UpwardNameReferenceSimulation,
     InstanceScopeNameResolvesDownwardFromParent) {
  // A scope_name.item_name reference whose leading scope_name is a sibling
  // instance resolves by first stepping up to the reference's enclosing
  // scope, locating the named instance there, and then resolving the item
  // downward from that instance. Here probe reads sib.v, where sib is a peer
  // instance sharing the enclosing module mid; the value must be drawn from
  // that sibling instance rather than from probe's own scope.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  integer v;\n"
      "  initial v = 77;\n"
      "endmodule\n"
      "module probe;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    #1;\n"
      "    r = sib.v;\n"
      "  end\n"
      "endmodule\n"
      "module mid;\n"
      "  probe p1();\n"
      "  sub sib();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("m1.p1.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 77u);
}

TEST(UpwardNameReferenceSimulation, UpwardSearchUsesEnclosingModuleNotSibling) {
  // The upward search visits enclosing module scopes only; it must not reach
  // sideways into a sibling instance. Here child's reference parent.v resolves
  // to the enclosing module parent's own variable (88), even though a sibling
  // instance other_inst also declares a variable named v (5).
  SimFixture f;
  auto* design = ElaborateSrc(
      "module other;\n"
      "  integer v;\n"
      "  initial v = 5;\n"
      "endmodule\n"
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
      "  other other_inst();\n"
      "  initial v = 88;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("c1.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 88u);
}

}  // namespace
