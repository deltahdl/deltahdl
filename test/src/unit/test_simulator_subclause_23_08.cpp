#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
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

std::string ParentNamedObject(const std::string& decls,
                              const std::string& stmts,
                              const std::string& read) {
  return "module c;\n" + decls + "  initial begin\n" + stmts +
         "    #1 $display(\"%0d\", " + read +
         ");\n  end\nendmodule\n"
         "module m;\n  int x = 9;\n  c c1();\nendmodule\n";
}

TEST(UpwardSearchStopsAtAnObject, AStructureLackingTheMemberIsReported) {
  SimFixture f;
  RunCaptureAllTops(ParentNamedObject("  struct {int y;} m;\n", "", "m.x"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the structure of 'm' has no member named 'x'", 4,
                            "23.7"));
}

TEST(UpwardSearchStopsAtAnObject,
     DISABLED_AnInitializedStructureMemberIsReadNotTheModules) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops(
          ParentNamedObject("  struct {int x;} m = '{5};\n", "", "m.x"), f),
      "5\n");
}

TEST(UpwardSearchStopsAtAnObject,
     AnAssignedStructureMemberIsReadNotTheModules) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(ParentNamedObject("  struct {int x;} m;\n",
                                                "    m.x = 6;\n", "m.x"),
                              f),
            "6\n");
}

TEST(UpwardSearchStopsAtAnObject, AUnionLackingTheMemberIsReported) {
  SimFixture f;
  RunCaptureAllTops(ParentNamedObject("  union {int y;} m;\n", "", "m.x"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the union of 'm' has no member named 'x'", 4,
                            "23.7"));
}

TEST(UpwardSearchStopsAtAnObject, AUnionMemberIsReadNotTheModules) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(ParentNamedObject("  union {int x;} m;\n",
                                                "    m.x = 6;\n", "m.x"),
                              f),
            "6\n");
}

TEST(UpwardSearchStopsAtAnObject, AClassLackingThePropertyIsReported) {
  SimFixture f;
  RunCaptureAllTops(
      ParentNamedObject("  class K;\n    int y;\n  endclass\n  K m;\n",
                        "    m = new;\n", "m.x"),
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'K' has no member named 'x'", 8, "8.5"));
}

TEST(UpwardSearchStopsAtAnObject, DISABLED_AClassPropertyIsReadNotTheModules) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                ParentNamedObject("  class K;\n    int x = 7;\n  endclass\n"
                                  "  K m;\n",
                                  "    m = new;\n", "m.x"),
                f),
            "7\n");
}

TEST(UpwardSearchStopsAtAnObject,
     DISABLED_ACovergroupLackingTheMemberIsReported) {
  SimFixture f;
  RunCaptureAllTops(
      ParentNamedObject("  int v;\n  covergroup cg;\n    cp: coverpoint v;\n"
                        "  endgroup\n  cg m = new;\n",
                        "", "m.x"),
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "covergroup 'cg' has no member named 'x'", 8,
                            "23.7"));
}

TEST(UpwardSearchStopsAtAnObject, ACovergroupMemberIsReadNotTheModules) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                ParentNamedObject("  int v;\n  covergroup cg;\n"
                                  "    x: coverpoint v {bins one = {1};}\n"
                                  "  endgroup\n  cg m = new;\n",
                                  "    v = 1;\n    m.sample();\n",
                                  "$rtoi(m.x.get_inst_coverage())"),
                f),
            "100\n");
}

TEST(UpwardItemReferenceRun, ATaskThroughTheDefinitionNameRunsInEachInstance) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                "module c;\n  initial #1 b.t;\nendmodule\n"
                "module b;\n  int i;\n  task t;\n    i = i + 1;\n  endtask\n"
                "  c c1();\nendmodule\n"
                "module top;\n  b x(), y();\n"
                "  initial #2 $display(\"%0d %0d\", x.i, y.i);\nendmodule\n",
                f),
            "1 1\n");
}

TEST(UpwardItemReferenceRun, ANamedBlockVariableOfTheEnclosingModuleIsRead) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                "module c;\n  initial #1 $display(\"%0d\", b.blk.v);\n"
                "endmodule\n"
                "module b;\n  initial begin : blk\n    static int v = 5;\n"
                "  end\n  c c1();\nendmodule\n",
                f),
            "5\n");
}

TEST(UpwardItemReferenceRun, EachCopyOfTheEnclosingModuleTakesItsOwnWrite) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops(
          "module a;\n  integer i;\n  b a_b1();\nendmodule\n"
          "module b;\n  integer i;\n  c b_c1(), b_c2();\nendmodule\n"
          "module c;\n  integer i;\n"
          "  initial begin\n    i = 1;\n    b.i = 1;\n  end\n"
          "endmodule\n"
          "module d;\n  integer i;\n  b d_b1();\nendmodule\n"
          "module top;\n  a a();\n  d d();\n"
          "  initial #1 $display(\"%0d %0d %0d %0d\", a.a_b1.i, d.d_b1.i, "
          "a.i, a.a_b1.b_c2.i);\nendmodule\n",
          f),
      "1 1 x 1\n");
}

TEST(UpwardItemReferenceRun, AContinuousAssignmentReadsAnUpwardNet) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops("module c;\n  wire w;\n  assign w = b.m;\n"
                              "  initial #1 $display(\"%b\", w);\nendmodule\n"
                              "module b;\n  wire m = 1;\n  c c1();\n"
                              "endmodule\n",
                              f),
            "1\n");
}

TEST(UpwardItemReferenceRun, AContinuousAssignmentDrivesAnUpwardNet) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops("module c;\n  assign b.m = 1;\nendmodule\n"
                              "module b;\n  wire m;\n  c c1();\n"
                              "  initial #1 $display(\"%b\", m);\nendmodule\n",
                              f),
            "1\n");
}

TEST(UpwardItemReferenceRun, ALowerModulesFunctionReadsAnUpwardVariable) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops("module c;\n"
                        "  function int rd();\n    return b.v;\n  endfunction\n"
                        "  initial #1 $display(\"%0d\", rd());\nendmodule\n"
                        "module b;\n  int v = 9;\n  c c1();\nendmodule\n",
                        f),
      "9\n");
}

std::string OwnNameAssertion(const std::string& keyword,
                             const std::string& name, const std::string& items,
                             const std::string& rest) {
  return keyword + " " + name + ";\n  logic clk = 0, a = 1;\n  int n = 0;\n" +
         items +
         "  initial begin\n    #1 clk = 1;\n    #1 clk = 0;\n"
         "    #1 clk = 1;\n    #1 $display(\"%0d\", n);\n  end\nend" +
         keyword + "\n" + rest;
}

std::string FirstLine(const std::string& out) {
  return out.substr(0, out.find('\n') + 1);
}

TEST(OwnNameInAModuleAssertion, ARootedNameIsAccepted) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                OwnNameAssertion(
                    "module", "m",
                    "  assert property (@(posedge clk) $root.m.a) n++;\n", ""),
                f),
            "2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OwnNameInAModuleAssertion, AProceduralAssertionAcceptsTheOwnName) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                OwnNameAssertion(
                    "module", "m",
                    "  always @(posedge clk) assert property (m.a) n++;\n", ""),
                f),
            "2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OwnNameInAModuleAssertion, DISABLED_TheOwnNameOfATopLevelModule) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops(
          OwnNameAssertion("module", "m",
                           "  assert property (@(posedge clk) m.a) n++;\n", ""),
          f),
      "2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OwnNameInAModuleAssertion, DISABLED_TheOwnNameOfAnInstantiatedModule) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops(
          OwnNameAssertion("module", "sub",
                           "  assert property (@(posedge clk) sub.a) n++;\n",
                           "module top;\n  sub s0();\nendmodule\n"),
          f),
      "2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OwnNameInAModuleAssertion, DISABLED_TheEnclosingInstanceName) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops(
          OwnNameAssertion("module", "sub",
                           "  assert property (@(posedge clk) s0.a) n++;\n",
                           "module top;\n  sub s0();\nendmodule\n"),
          f),
      "2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OwnNameInAModuleAssertion, DISABLED_InASequenceAndAPropertyDeclaration) {
  SimFixture f;
  EXPECT_EQ(FirstLine(RunCaptureAllTops(
                OwnNameAssertion("module", "m",
                                 "  sequence s;\n    @(posedge clk) m.a;\n"
                                 "  endsequence\n"
                                 "  property p;\n    @(posedge clk) m.a;\n"
                                 "  endproperty\n"
                                 "  cover property (s) n++;\n"
                                 "  cover property (p) n++;\n",
                                 ""),
                f)),
            "4\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OwnNameInAModuleAssertion, DISABLED_InAnInterface) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops(
          OwnNameAssertion("interface", "ii",
                           "  assert property (@(posedge clk) ii.a) n++;\n"
                           "  assert property (@(posedge clk) u.a) n++;\n",
                           "module top;\n  ii u();\nendmodule\n"),
          f),
      "4\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OwnNameInAModuleAssertion, DISABLED_InAProgram) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops(
          OwnNameAssertion("program", "pp",
                           "  assert property (@(posedge clk) pp.a) n++;\n"
                           "  assert property (@(posedge clk) u.a) n++;\n",
                           "module top;\n  pp u();\nendmodule\n"),
          f),
      "4\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OwnNameInAModuleAssertion, DISABLED_InAChecker) {
  SimFixture f;
  RunCaptureAllTops(
      "checker ck(logic clk);\n  logic a = 1;\n"
      "  assert property (@(posedge clk) ck.a);\n"
      "  assert property (@(posedge clk) u.a);\nendchecker\n"
      "module top;\n  logic clk = 0;\n  ck u(clk);\nendmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OwnNameInAModuleAssertion,
     DISABLED_InDisableIffAClockingEventAndASequenceArgument) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                OwnNameAssertion("module", "m",
                                 "  sequence s(x);\n    x;\n  endsequence\n"
                                 "  assert property (@(posedge m.clk) "
                                 "disable iff (!m.a) s(m.a)) n++;\n",
                                 ""),
                f),
            "2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
