#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceSim, NullReferenceEndsTheRun) {
  SimFixture f;
  std::string out = RunCapture(
      "interface SBus; logic a; endinterface\n"
      "class C;\n"
      "  virtual SBus vif;\n"
      "  task poke(); vif.a = 1; endtask\n"
      "endclass\n"
      "module top;\n"
      "  SBus s();\n"
      "  virtual SBus v;\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    c.poke();\n"
      "    $display(\"should not run\");\n"
      "  end\n"
      "  initial #5 $display(\"nor this %0d\", v.a);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference through a null virtual interface", 4,
                            "25.9"));
}

TEST(VirtualInterfaceSim, NullAssignmentTargetReportsOnce) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc; logic a; endinterface\n"
      "module top;\n"
      "  virtual ifc v;\n"
      "  initial begin $display(\"before\"); #2 v.a = 1; "
      "$display(\"after\"); end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "before\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference through a null virtual interface", 4,
                            "25.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(VirtualInterfaceSim, PropertyComparedWithFormalInMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "class Cmp;\n"
                       "  virtual SBus vif;\n"
                       "  function bit is(virtual SBus o); return vif == o; "
                       "endfunction\n"
                       "  function bit isnt(virtual SBus o); return vif != o; "
                       "endfunction\n"
                       "endclass\n"
                       "module top;\n"
                       "  SBus s1(), s2();\n"
                       "  Cmp c;\n"
                       "  initial begin\n"
                       "    c = new;\n"
                       "    c.vif = s1;\n"
                       "    $display(\"same=%0d other=%0d ne=%0d\", c.is(s1), "
                       "c.is(s2), c.isnt(s1));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "same=1 other=0 ne=0\n");
}

TEST(VirtualInterfaceSim, FunctionResultComparesEqualToItsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "class Pool;\n"
                       "  virtual SBus vs[2];\n"
                       "  function virtual SBus pick(int i); return vs[i]; "
                       "endfunction\n"
                       "endclass\n"
                       "module top;\n"
                       "  SBus s0(), s1();\n"
                       "  Pool p;\n"
                       "  virtual SBus got;\n"
                       "  initial begin\n"
                       "    p = new; p.vs[0] = s0; p.vs[1] = s1;\n"
                       "    got = p.pick(1);\n"
                       "    got.a = 50;\n"
                       "    $display(\"got=%0d call=%0d other=%0d a=%0d\", "
                       "got == s1, p.pick(0) == s0, p.pick(0) == s1, s1.a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "got=1 call=1 other=0 a=50\n");
}

TEST(VirtualInterfaceSim, GenerateBlockInstancePathIsASource) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "module top;\n"
                       "  for (genvar i = 0; i < 3; i++) begin : g\n"
                       "    SBus s();\n"
                       "  end\n"
                       "  virtual SBus v;\n"
                       "  initial begin\n"
                       "    v = g[1].s; v.a = 10;\n"
                       "    v = g[2].s; v.a = 20;\n"
                       "    v = g[0].s; v.a = 30;\n"
                       "    $display(\"%0d %0d %0d\", g[0].s.a, g[1].s.a, "
                       "g[2].s.a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "30 10 20\n");
}

TEST(VirtualInterfaceSim, TopHeadedInstancePathCompares) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "module top;\n"
                       "  SBus s1(), s2();\n"
                       "  virtual SBus v;\n"
                       "  initial begin\n"
                       "    v = s1;\n"
                       "    $display(\"hier=%0d other=%0d\", v == top.s1, "
                       "v == top.s2);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "hier=1 other=0\n");
}

TEST(VirtualInterfaceSim, ProgramInterfacePortIsASource) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "program P(SBus b);\n"
                       "  virtual SBus v;\n"
                       "  initial begin\n"
                       "    v = b;\n"
                       "    #3 v.a = 5;\n"
                       "    $display(\"prog sees %0d t=%0t\", top.s.a, "
                       "$time);\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  SBus s();\n"
                       "  P p(s);\n"
                       "endmodule\n",
                       f),
            "prog sees 5 t=3\n");
}

TEST(VirtualInterfaceSim, ModuleInterfacePortIsASource) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "module M(SBus b);\n"
                       "  virtual SBus v;\n"
                       "  initial begin\n"
                       "    v = b;\n"
                       "    v.a = 7;\n"
                       "    #1 $display(\"a=%0d eq=%0d\", top.s.a, v == b);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  SBus s();\n"
                       "  M m(s);\n"
                       "endmodule\n",
                       f),
            "a=7 eq=1\n");
}

TEST(VirtualInterfaceSim, InstanceArrayElementIsASource) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "module top;\n"
                       "  SBus s[0:1]();\n"
                       "  virtual SBus v;\n"
                       "  initial begin\n"
                       "    s[1].a = 5;\n"
                       "    v = s[1];\n"
                       "    v.a = 6;\n"
                       "    $display(\"s1.a=%0d v.a=%0d eq=%0d\", s[1].a, "
                       "v.a, v == s[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "s1.a=6 v.a=6 eq=1\n");
}

TEST(VirtualInterfaceSim, ModuleItemInitializerNamesAnInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "module top;\n"
                       "  SBus s();\n"
                       "  virtual SBus v = s;\n"
                       "  task automatic t();\n"
                       "    virtual SBus lv = v;\n"
                       "    lv.a = 8;\n"
                       "    $display(\"a=%0d eq=%0d v.a=%0d\", s.a, lv == s, "
                       "v.a);\n"
                       "  endtask\n"
                       "  initial t();\n"
                       "endmodule\n",
                       f),
            "a=8 eq=1 v.a=8\n");
}

TEST(VirtualInterfaceSim, FixedArrayElementReachesItsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "module top;\n"
                       "  SBus s0(), s1();\n"
                       "  virtual SBus v[2];\n"
                       "  initial begin\n"
                       "    v[0] = s0; v[1] = s1;\n"
                       "    v[0].a = 7; s1.a = 8;\n"
                       "    $display(\"v0.a=%0d s0.a=%0d v1.a=%0d\", v[0].a, "
                       "s0.a, v[1].a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "v0.a=7 s0.a=7 v1.a=8\n");
}

TEST(VirtualInterfaceSim, QueueAndAssocElementsReachTheirInstances) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "module top;\n"
                       "  SBus s0(), s1();\n"
                       "  virtual SBus q[$];\n"
                       "  virtual SBus m[string];\n"
                       "  initial begin\n"
                       "    q.push_back(s0); q.push_back(s1);\n"
                       "    q[1].a = 22; m[\"two\"] = s1;\n"
                       "    $display(\"s1.a=%0d m=%0d\", s1.a, m[\"two\"].a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "s1.a=22 m=22\n");
}

TEST(VirtualInterfaceSim, ArrayPropertyElementReachesItsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface SBus; int a; endinterface\n"
                       "class Env;\n"
                       "  virtual SBus vifs[2];\n"
                       "  function void drive_all(); foreach (vifs[i]) "
                       "vifs[i].a = 100 + i; endfunction\n"
                       "endclass\n"
                       "module top;\n"
                       "  SBus s0(), s1();\n"
                       "  Env e;\n"
                       "  initial begin\n"
                       "    e = new; e.vifs[0] = s0; e.vifs[1] = s1;\n"
                       "    e.drive_all();\n"
                       "    $display(\"%0d %0d\", s0.a, s1.a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "100 101\n");
}

TEST(VirtualInterfaceSim, FunctionCalledThroughVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface calc_if;\n"
                       "  int base = 40;\n"
                       "  function int add(int k); return base + k; "
                       "endfunction\n"
                       "endinterface\n"
                       "module top;\n"
                       "  calc_if c();\n"
                       "  virtual calc_if v;\n"
                       "  initial begin\n"
                       "    v = c;\n"
                       "    $display(\"vif add=%0d\", v.add(20));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "vif add=60\n");
}

TEST(VirtualInterfaceSim, SubroutinesCalledThroughClassProperties) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface calc_if;\n"
                       "  int base = 40;\n"
                       "  function int add(int k); return base + k; "
                       "endfunction\n"
                       "  task write(int d); #7 base = d; endtask\n"
                       "endinterface\n"
                       "class Agent;\n"
                       "  virtual calc_if vif;\n"
                       "  static virtual calc_if svif;\n"
                       "  function new(virtual calc_if v); vif = v; svif = v; "
                       "endfunction\n"
                       "  task go();\n"
                       "    vif.write(88);\n"
                       "    $display(\"method t=%0t add=%0d static=%0d\", "
                       "$time, vif.add(1), Agent::svif.add(2));\n"
                       "  endtask\n"
                       "endclass\n"
                       "module top;\n"
                       "  calc_if c();\n"
                       "  Agent a;\n"
                       "  initial begin\n"
                       "    a = new(c);\n"
                       "    a.go();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "method t=7 add=89 static=90\n");
}

}  // namespace
