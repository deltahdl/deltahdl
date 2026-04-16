#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- Rule (a): First component is a data object → member select ---

TEST(DottedNameSimulation, StructMemberSelectReadsField) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    s = 16'hAB_CD;\n"
      "    result = s.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0xABu);
}

TEST(DottedNameSimulation, StructMemberSelectWritesField) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s = 16'h0000;\n"
      "    s.hi = 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("s");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0xFF00u);
}

TEST(DottedNameSimulation, UnionMemberSelectReadsField) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } u_t;\n"
      "  u_t u;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    u.a = 8'h42;\n"
      "    result = u.b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x42u);
}

TEST(DottedNameSimulation, ClassMemberSelectReadsProperty) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C;\n"
      "    int val;\n"
      "    function new;\n"
      "      val = 99;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    result = obj.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(DottedNameSimulation, NestedStructMemberSelectReadsDeepField) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; } inner_t;\n"
      "  typedef struct packed { inner_t sub; } outer_t;\n"
      "  outer_t o;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    o.sub.x = 8'h77;\n"
      "    result = o.sub.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x77u);
}

// --- Rule (b): First component is a scope name → hierarchical name ---

TEST(DottedNameSimulation, InstanceScopeReadsHierarchicalName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] val;\n"
      "  initial val = 8'd42;\n"
      "endmodule\n"
      "module t;\n"
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

TEST(DottedNameSimulation, InstanceScopeWritesHierarchicalName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] val;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  initial c1.val = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("c1.val");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 55u);
}

// --- Rules (a) and (b) coexist in one module ---

TEST(DottedNameSimulation, MemberSelectAndHierarchicalNameInSameModule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] sig;\n"
      "  initial sig = 8'd10;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [7:0] r1, r2;\n"
      "  initial begin\n"
      "    s = 16'h00_33;\n"
      "    r1 = s.y;\n"
      "    #1;\n"
      "    r2 = c1.sig;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v1 = f.ctx.FindVariable("r1");
  ASSERT_NE(v1, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 0x33u);
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v2->value.ToUint64(), 10u);
}

}  // namespace
