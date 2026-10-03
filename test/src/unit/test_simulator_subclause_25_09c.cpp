#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §25.9: using a virtual interface that represents no instance is a fatal
// run-time error. The write through the class's null property is reported at
// line 4, and the run ends there: the statement after the call does not run,
// and the second process, which would read through another null virtual
// interface at time 5, is never reached. Before the run was ended, both lines
// printed and the read drew a second report.
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

// §25.9: two virtual interfaces are equal when they represent the same
// instance, wherever they are compared. In a method, the property `vif` set
// to s1 equals the formal bound to s1, not the one bound to s2, and `!=`
// answers the opposite. Before the operands were compared by handle, the
// property was read as an instance's name, found none, and compared as an
// unbound virtual interface: `same=0 other=0 ne=1`.
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

// §25.9: a virtual interface a class function returns represents the
// instance it was set to, so it equals that instance whether it was first
// held in a variable, `got == s1`, or is compared as the call's own value,
// `p.pick(0) == s0`, and not another, `p.pick(0) == s1`. The write through
// it reaching s1.a shows the handle arrived. Each comparison is printed on
// its own: their sum is a 1-bit expression (§11.6.1), in which 1 + 1 is 0.
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

// §25.9 with §27.4: an interface instance in a loop generate block is named
// `g[1].s`, and a virtual interface assigned that path represents it, so each
// write lands in its own instance. Before the path evaluated to a handle,
// every write reached nothing and all three read 0.
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

// §25.9 with §23.6: `top.s1` names the instance s1 from the top, so the
// virtual interface set to s1 equals it and not s2. Before the path evaluated
// to a handle, `v == top.s1` answered 0.
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

// §25.9 with §25.3.2: an interface port denotes the instance connected to
// it, so a program's virtual interface assigned its port b represents top.s,
// and the write through it at time 3 reaches top.s.a. Before the port's name
// evaluated to that instance's handle, the write reached nothing and the
// program read 0.
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

// §25.9 with §25.3.2: the same through a module's interface port, compared
// as well as written: `v == b` holds and the write through v is the
// connected instance's.
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

// §25.9 with §23.3.3.5: each element of an array of interface instances is
// an instance, so `v = s[1]` represents s[1]: the write through v reaches
// s[1].a and v equals s[1]. Before the select evaluated to that instance's
// handle, v represented nothing.
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

// §25.9 with §6.8: a virtual interface declared with an initializer naming an
// instance, `virtual SBus v = s;`, represents it before any procedure runs,
// so a task's local initialized from v represents s too. Before the
// instance was registered ahead of the module's variables, v stayed null and
// every reference through it was reported.
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

// §25.9 with §7.4: an element of a fixed array of virtual interfaces is used
// as the virtual interface it holds, so `v[0].a` is s0's a, written and read,
// and `v[1].a` is s1's. Before the element was resolved as a virtual
// interface, the write was lost and every read gave 0.
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

// §25.9 with §7.10 and §7.8: the same for an element of a queue, `q[1].a`
// written, and of an associative array, `m["two"].a` read.
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

// §25.9 with §7.4.2: an element of an array property of virtual interfaces,
// `vifs[i]` in a method, reaches the instance it holds.
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

// §25.9 with §25.7: a function of an interface called through a virtual
// interface held in a module variable is the function of the instance it
// represents, reading that instance's `base`. Before the callee's head was
// resolved as a virtual interface, the call ran nothing and answered 0.
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

// §25.9 with §25.7: the same through a class's property, from a method: the
// task's delay of 7 runs and its write reaches the instance's base, which
// the function then reads, and through a static property named by the class
// scope, `Agent::svif.add(2)`. Before this the task took no time and both
// calls answered 0.
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
