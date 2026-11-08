#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(UpwardNameReferenceSimulation, UpwardReadReturnsEnclosingValue) {
  SimFixture f;
  auto* v = RunAndFindVar(
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
      f, "c1.r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(UpwardNameReferenceSimulation, UpwardWriteUpdatesEnclosingVariable) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  initial parent.v = 99;\n"
      "endmodule\n"
      "module parent;\n"
      "  integer v;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(UpwardNameReferenceSimulation, CanonicalExampleUpwardWriteHitsEnclosing) {
  SimFixture f;
  auto* b_i = RunAndFindVar(
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
      f, "a_b1.i");
  ASSERT_NE(b_i, nullptr);
  EXPECT_EQ(b_i->value.ToUint64(), 9u);
  auto* c_i = f.ctx.FindVariable("a_b1.b_c1.i");
  ASSERT_NE(c_i, nullptr);
  EXPECT_EQ(c_i->value.ToUint64(), 1u);
}

TEST(UpwardNameReferenceSimulation, UpwardReferenceAcrossTwoLevels) {
  SimFixture f;
  auto* v = RunAndFindVar(
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
      f, "m1.l1.r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 55u);
}

TEST(UpwardNameReferenceSimulation,
     InstanceScopeNameResolvesDownwardFromParent) {
  SimFixture f;
  auto* r = RunAndFindVar(
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
      f, "m1.p1.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 77u);
}

TEST(UpwardNameReferenceSimulation, UpwardReferenceByEnclosingInstanceName) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module leaf;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    #1;\n"
      "    r = m1.v;\n"
      "  end\n"
      "endmodule\n"
      "module mid;\n"
      "  integer v;\n"
      "  leaf l1();\n"
      "  initial v = 33;\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "endmodule\n",
      f, "m1.l1.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 33u);
}

TEST(UpwardNameReferenceSimulation, UpwardNetReferenceReadsDrivenValue) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module child;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    #1;\n"
      "    r = parent.n;\n"
      "  end\n"
      "endmodule\n"
      "module parent;\n"
      "  wire [7:0] n;\n"
      "  assign n = 8'hA5;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "c1.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0xA5u);
}

TEST(UpwardNameReferenceSimulation, UpwardParameterReferenceReadsValue) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module child;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    #1;\n"
      "    r = parent.P;\n"
      "  end\n"
      "endmodule\n"
      "module parent;\n"
      "  parameter int P = 8;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "c1.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 8u);
}

TEST(UpwardNameReferenceSimulation, UpwardPortReferenceReadsDrivenValue) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module child;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    #1;\n"
      "    r = parent.p;\n"
      "  end\n"
      "endmodule\n"
      "module parent(input logic [7:0] p);\n"
      "  child c1();\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] s = 8'h3C;\n"
      "  parent pi(.p(s));\n"
      "endmodule\n",
      f, "pi.c1.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0x3Cu);
}

TEST(UpwardNameReferenceSimulation, UpwardSearchUsesEnclosingModuleNotSibling) {
  SimFixture f;
  auto* r = RunAndFindVar(
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
      f, "c1.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 88u);
}

TEST(UpwardNameReferenceSimulation,
     CallThroughAnEnclosingModulesNameRunsInTheNearestInstance) {
  SimFixture f;
  auto* first = RunAndFindVar(
      "module leaf;\n"
      "  int y;\n"
      "  initial #1 y = mid.f(2);\n"
      "endmodule\n"
      "module inner;\n"
      "  leaf t();\n"
      "endmodule\n"
      "module mid #(parameter int G = 5);\n"
      "  int g = G;\n"
      "  function int f(int x);\n"
      "    return x + g;\n"
      "  endfunction\n"
      "  inner u();\n"
      "endmodule\n"
      "module top;\n"
      "  mid #(5) m1();\n"
      "  mid #(10) m2();\n"
      "endmodule\n",
      f, "m1.u.t.y");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->value.ToUint64(), 7u);
  auto* second = f.ctx.FindVariable("m2.u.t.y");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->value.ToUint64(), 12u);
}

TEST(UpwardNameReferenceSimulation, DottedNameHeadedByAnEnclosingNamedBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial begin : outer\n"
                       "    begin : inner\n"
                       "      reg [3:0] x;\n"
                       "      x = 4;\n"
                       "    end\n"
                       "    $display(\"%0d\", inner.x);\n"
                       "  end\n"
                       "  task tk;\n"
                       "    begin : b\n"
                       "      logic [3:0] r;\n"
                       "      b.r = 5;\n"
                       "      $display(\"%0d\", r);\n"
                       "      r = 7;\n"
                       "      $display(\"%0d %0d %0d\", r, b.r, tk.b.r);\n"
                       "    end\n"
                       "  endtask\n"
                       "  initial begin : caller\n"
                       "    #2 tk;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4\n5\n7 7 7\n");
}

}  // namespace
