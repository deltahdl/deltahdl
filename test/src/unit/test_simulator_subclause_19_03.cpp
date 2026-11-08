#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, CreateGroupAndFind) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg_addr");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->name, "cg_addr");
  EXPECT_EQ(db.GroupCount(), 1u);
  auto* found = db.FindGroup("cg_addr");
  EXPECT_EQ(found, g);
}

TEST(Coverage, FindNonexistentGroupReturnsNull) {
  CoverageDB db;
  EXPECT_EQ(db.FindGroup("missing"), nullptr);
}

TEST(Coverage, MultipleGroupInstances) {
  CoverageDB db;
  auto* g1 = db.CreateGroup("cg1");
  auto* g2 = db.CreateGroup("cg2");
  EXPECT_EQ(db.GroupCount(), 2u);
  EXPECT_NE(g1, g2);
  EXPECT_EQ(db.FindGroup("cg1")->name, "cg1");
  EXPECT_EQ(db.FindGroup("cg2")->name, "cg2");
}

TEST(CovergroupInstanceSim, ClockingEventSamplesEachEdge) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  logic clk = 0, a = 1;\n"
          "  bit a_d1 = 0;\n"
          "  always #5 clk = ~clk;\n"
          "  always_ff @(posedge clk) a_d1 <= a;\n"
          "  covergroup cg @(posedge clk);\n"
          "    cp: coverpoint a { bins lo = {1'b0}; bins hi = {1'b1}; }\n"
          "    cpd: coverpoint a_d1 { bins lo = {1'b0}; bins hi = {1'b1}; }\n"
          "    option.per_instance = 1;\n"
          "  endgroup\n"
          "  cg cg_1 = new();\n"
          "  initial begin\n"
          "    #12 a = 0; #20 a = 1; #20;\n"
          "    $display(\"cov=%0d\", $rtoi(cg_1.get_inst_coverage()));\n"
          "    $finish;\n"
          "  end\n"
          "endmodule\n",
          f),
      "cov=100\n$finish at time 52\n");
}

TEST(CovergroupInstanceSim, FormalDefaultUsedWithoutActual) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [3:0] v; int n, t;\n"
                 "  covergroup cg (int hi = 5);\n"
                 "    coverpoint v { bins b = {[0:hi]}; bins c = {15}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    v = 4; c.sample();\n"
                 "    void'(c.get_inst_coverage(n, t));\n"
                 "    $display(\"n=%0d t=%0d\", n, t);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "n=1 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, RefFormalSamplesActualAtEachSample) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int va; int n, t;\n"
                       "  covergroup cg (ref int x);\n"
                       "    coverpoint x { bins b = {7}; bins z = {1}; }\n"
                       "  endgroup\n"
                       "  cg c = new(va);\n"
                       "  initial begin\n"
                       "    va = 7; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, ProceduralNewBuildsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v;\n"
                       "  covergroup cg; coverpoint v { bins lo = {0}; bins hi "
                       "= {3}; } endgroup\n"
                       "  cg c;\n"
                       "  initial begin c = new; v = 0; c.sample(); "
                       "$display(\"cov=%0.2f\", c.get_inst_coverage()); end\n"
                       "endmodule\n",
                       f),
            "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, ImportedPackageCovergroupBuildsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  bit [1:0] pv;\n"
                       "  covergroup pcg; coverpoint pv { bins lo = {0}; bins "
                       "hi = {3}; bins z = {2}; } endgroup\n"
                       "endpackage\n"
                       "module top;\n"
                       "  import p::*;\n"
                       "  pcg c = new; int n, t;\n"
                       "  initial begin pv = 0; c.sample(); "
                       "void'(c.get_inst_coverage(n, t)); "
                       "$display(\"n=%0d t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=3\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim,
     PackageCovergroupByScopeOrNamedImportBuildsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  bit [1:0] pv;\n"
                       "  covergroup pcg; coverpoint pv { bins lo = {0}; bins "
                       "hi = {3}; } endgroup\n"
                       "endpackage\n"
                       "module top;\n"
                       "  p::pcg c = new;\n"
                       "  import p::pv; import p::pcg;\n"
                       "  pcg d = new; int n, t;\n"
                       "  initial begin pv = 3; c.sample(); d.sample(); "
                       "void'(c.get_inst_coverage(n, t)); "
                       "$write(\"n=%0d t=%0d \", n, t); "
                       "void'(d.get_inst_coverage(n, t)); "
                       "$display(\"n=%0d t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=2 n=1 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, BeginBlockEventSamplesAsTaskStarts) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  task tk; v = 3; endtask\n"
                       "  covergroup cg @@(begin tk);\n"
                       "    coverpoint v { bins lo = {0}; bins z = {2}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin v = 0; tk(); "
                       "void'(c.get_inst_coverage(n, t)); "
                       "$display(\"n=%0d t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, OrJoinedBlockEventsSampleFunctionEndAndBlockBegin) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v; int n, t;\n"
                 "  function void fn; v = 3; endfunction\n"
                 "  covergroup cg @@(end fn or begin blk);\n"
                 "    coverpoint v { bins one = {1}; bins three = {3}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin v = 0; fn(); v = 1;\n"
                 "    begin : blk v = 2; end\n"
                 "    void'(c.get_inst_coverage(n, t));\n"
                 "    $display(\"n=%0d t=%0d\", n, t);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "n=2 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, BlockEventSamplesOnlyTheInstanceRunningTheTask) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(bit GO = 0);\n"
                       "  bit [1:0] v;\n"
                       "  task tk; endtask\n"
                       "  covergroup cg @@(begin tk);\n"
                       "    coverpoint v { bins lo = {0}; bins hi = {3}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial if (GO) tk();\n"
                       "endmodule\n"
                       "module top;\n"
                       "  m #(1) u1(); m u2();\n"
                       "  initial #1 $display(\"%0.2f %0.2f\", "
                       "u1.c.get_inst_coverage(), u2.c.get_inst_coverage());\n"
                       "endmodule\n",
                       f),
            "50.00 0.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, RebuiltInstanceSamplesOncePerBlockEvent) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  task go; endtask\n"
                       "  covergroup cg @@(end go);\n"
                       "    option.at_least = 2;\n"
                       "    coverpoint v { bins b = {2}; bins e = {1}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin c = new; v = 2; go();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=0 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, DisabledBlockTaskOrForkTriggersNoEndEvent) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  task tk; v = 2; disable tk; v = 0; endtask\n"
                       "  covergroup cg @@(end blk or end tk or end fk);\n"
                       "    coverpoint v { bins b[] = {[0:3]}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    for (int i = 0; i < 2; i++) begin : blk\n"
                       "      v = i; if (i == 0) disable blk;\n"
                       "    end\n"
                       "    tk();\n"
                       "    fork : fk begin v = 3; disable fk; end join\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 t=4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, CopiedHandleAndFormalReachTheInstance) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins a = {1}; bins b = {2}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  cg d;\n"
                 "  function void f(cg h); h.sample(); endfunction\n"
                 "  initial begin\n"
                 "    v = 1; d = c; d.sample();\n"
                 "    $write(\"copy=%0.2f \", c.get_inst_coverage());\n"
                 "    v = 2; f(c);\n"
                 "    $display(\"formal=%0.2f\", c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "copy=50.00 formal=100.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, SecondNewLeavesTheCopiedInstance) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins a = {1}; bins b = {2}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  cg d;\n"
                 "  initial begin\n"
                 "    v = 1; c.sample(); d = c; c = new; v = 2; c.sample();\n"
                 "    $display(\"%0.2f %0.2f\", d.get_inst_coverage(),\n"
                 "             c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "50.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, StrobedCovergroupSamplesInPostponedRegion) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit clk; bit [1:0] v;\n"
                 "  covergroup cg @(posedge clk);\n"
                 "    type_option.strobe = 1;\n"
                 "    coverpoint v { bins b = {2}; bins c = {3}; }\n"
                 "  endgroup\n"
                 "  covergroup cg2 @(posedge clk);\n"
                 "    coverpoint v { bins b = {2}; bins c = {3}; }\n"
                 "  endgroup\n"
                 "  cg c = new; cg2 c2 = new;\n"
                 "  initial begin\n"
                 "    v = 1; #1 clk = 1; #0 v = 2;\n"
                 "    #1 $display(\"%0.2f %0.2f\", c.get_inst_coverage(),\n"
                 "                c2.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "50.00 0.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, StrobedCovergroupSamplesOncePerTimeSlot) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit clk; bit [1:0] v; int n, t;\n"
                 "  covergroup cg @(clk);\n"
                 "    type_option.strobe = 1;\n"
                 "    coverpoint v { bins b[] = {[0:3]}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    #1 clk = 1; v = 1; #0 clk = 0; v = 2; #0 clk = 1;\n"
                 "    v = 3;\n"
                 "    #1 void'(c.get_inst_coverage(n, t));\n"
                 "    $display(\"n=%0d t=%0d\", n, t);\n"
                 "    v = 0; c.sample(); void'(c.get_inst_coverage(n, t));\n"
                 "    $display(\"n=%0d t=%0d\", n, t);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "n=1 t=4\nn=2 t=4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, StrobedEmbeddedCovergroupSamplesInPostponedRegion) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit clk;\n"
                       "  class C;\n"
                       "    bit [1:0] x;\n"
                       "    covergroup cg @(posedge clk);\n"
                       "      type_option.strobe = 1;\n"
                       "      coverpoint x { bins b = {2}; bins c = {3}; }\n"
                       "    endgroup\n"
                       "    function new(); cg = new; endfunction\n"
                       "  endclass\n"
                       "  C o;\n"
                       "  initial begin\n"
                       "    o = new; o.x = 1; #1 clk = 1; #0 o.x = 2;\n"
                       "    #1 $display(\"%0.2f\", o.cg.get_inst_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, ArrayElementHoldsTheInstanceNewBuilds) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins a = {1}; bins b = {2}; }\n"
                 "  endgroup\n"
                 "  cg arr[2];\n"
                 "  initial begin\n"
                 "    arr[0] = new; arr[1] = new; v = 1; arr[1].sample();\n"
                 "    $display(\"%0.2f %0.2f\", arr[0].get_inst_coverage(),\n"
                 "             arr[1].get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, ClassPropertyHoldsTheInstanceNewBuilds) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk;\n"
                 "  covergroup pcg with function sample(int a);\n"
                 "    coverpoint a { bins one = {1}; bins two = {2}; }\n"
                 "  endgroup\n"
                 "endpackage\n"
                 "module top;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins a = {1}; bins b = {2}; }\n"
                 "  endgroup\n"
                 "  class K;\n"
                 "    cg p;\n"
                 "    pk::pcg q;\n"
                 "    function new(); p = new; q = new; endfunction\n"
                 "  endclass\n"
                 "  K k;\n"
                 "  initial begin\n"
                 "    k = new; v = 2; k.p.sample(); k.q.sample(1);\n"
                 "    $display(\"%0.2f %0.2f\", k.p.get_inst_coverage(),\n"
                 "             k.q.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "50.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, StaticPropertyHoldsTheInstanceNewBuilds) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins a = {1}; bins b = {2}; }\n"
                       "  endgroup\n"
                       "  class K; static cg s; endclass\n"
                       "  initial begin\n"
                       "    K::s = new; v = 1; K::s.sample();\n"
                       "    $display(\"%0.2f\", K::s.get_inst_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, AutomaticLocalHoldsTheInstanceNewBuilds) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins a = {1}; bins b = {2}; }\n"
                 "  endgroup\n"
                 "  function automatic real f();\n"
                 "    cg l = new;\n"
                 "    l.sample();\n"
                 "    return l.get_inst_coverage();\n"
                 "  endfunction\n"
                 "  task automatic t();\n"
                 "    cg l = new;\n"
                 "    v = 1; l.sample();\n"
                 "    $write(\"%0.2f \", l.get_inst_coverage());\n"
                 "  endtask\n"
                 "  initial begin\n"
                 "    automatic cg l = new;\n"
                 "    v = 2; l.sample();\n"
                 "    $write(\"%0.2f %0.2f \", f(), l.get_inst_coverage());\n"
                 "    t(); $display;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "50.00 50.00 50.00 \n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, CompletedNamedForkTriggersItsEndEvent) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  covergroup cg @@(end fk);\n"
                       "    coverpoint v { bins b[] = {[0:3]}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    fork : fk v = 2; #1 v = 3; join\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 t=4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, InheritedPropertyAndModuleVariableTakeNew) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins a = {1}; bins b = {2}; }\n"
                 "  endgroup\n"
                 "  cg m;\n"
                 "  class B; cg p; endclass\n"
                 "  class D extends B;\n"
                 "    function new(); p = new; m = new; endfunction\n"
                 "  endclass\n"
                 "  D d;\n"
                 "  initial begin\n"
                 "    d = new; v = 1; d.p.sample(); v = 2; m.sample();\n"
                 "    $display(\"%0.2f %0.2f\", d.p.get_inst_coverage(),\n"
                 "             m.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "50.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim,
     APackageCovergroupPropertyInitializedByNewHasAnInstance) {
  SimFixture f;
  auto out = RunCapture(
      "package pk;\n"
      "  covergroup cg with function sample(bit [1:0] x);\n"
      "    cp: coverpoint x;\n"
      "  endgroup\n"
      "endpackage\n"
      "import pk::*;\n"
      "class H;\n"
      "  cg g = new;\n"
      "  cg h;\n"
      "  function new(); h = new; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic H a = new;\n"
      "    a.g.sample(0); a.h.sample(0);\n"
      "    $display(\"%0.2f %0.2f\", a.g.get_inst_coverage(), "
      "a.h.get_inst_coverage());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "25.00 25.00\n");
}

TEST(CovergroupInstanceSim, ACompilationUnitCovergroupTypeHasInstances) {
  SimFixture f;
  auto out = RunCapture(
      "covergroup ucg with function sample(bit [1:0] x);\n"
      "  coverpoint x;\n"
      "endgroup\n"
      "class H;\n"
      "  ucg p;\n"
      "  function new(); p = new; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  ucg c = new;\n"
      "  initial begin\n"
      "    automatic H h = new;\n"
      "    automatic ucg l = new;\n"
      "    c.sample(1);\n"
      "    h.p.sample(1); h.p.sample(2);\n"
      "    l.sample(0); l.sample(1); l.sample(2);\n"
      "    $display(\"%0.2f %0.2f %0.2f\", c.get_inst_coverage(), "
      "h.p.get_inst_coverage(),\n"
      "             l.get_inst_coverage());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "25.00 50.00 75.00\n");
}

}  // namespace
