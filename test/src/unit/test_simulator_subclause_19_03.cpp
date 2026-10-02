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

// §19.3: a covergroup with a clocking event samples at each occurrence of the
// event. a is 1 at the posedges at 5 and 45 and 0 at 15, 25 and 35, and a_d1
// follows it a cycle later, so every bin of both coverpoints is hit.
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

// §19.3: a covergroup takes a function's tf_port_list, so a formal with a
// default takes it when new gives no actual: [0:hi] is [0:5], holding 4.
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

// §19.3: a ref formal refers to the actual, so a coverpoint over it samples
// va as it stands at the sample, 7, not the 0 it held at new().
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

// §19.3: new on the covergroup type builds an instance wherever the
// assignment stands, a procedural c = new among them.
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

// §19.3 with §26.3: a covergroup a package declares is a type its import makes
// visible, so `pcg c = new;` builds an instance sampling the package's pv, 0.
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

// §19.3 with §26.3: a package-qualified covergroup type needs no import, and
// an explicit import of the type's own name makes it visible past one naming
// another item, so `p::pcg c` and `pcg d` each build an instance.
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

// §19.3: a block event `begin t` samples as the task starts, so v is still
// the 0 it held before the call, not the 3 the task writes.
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

// §19.3: the terms of a block event joined by `or` each sample: `end fn`
// once the function has written 3, `begin blk` before the block writes 2.
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

// §19.3: a block event names the task of the instance the covergroup is in,
// so only u1's instance samples when u1 runs its task.
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

// §19.3: an instance built again by a second new is sampled once per block
// event, so with at_least 2 one call of the task covers no bin.
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

// §19.3: an end block event is not triggered when its block, task or named fork
// is disabled, so only the second pass of blk, which ends normally, samples.
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

// §19.3: a covergroup variable holds a handle, so a copy of it and a formal
// it is passed to reach the instance the variable holds.
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

// §19.3: each new builds a fresh instance, so a handle copied before the
// variable is given a second instance still reaches the first.
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

// §19.3 with §19.7.1: a covergroup whose strobe option is set samples in the
// Postponed region of the slot its clocking event occurred in, so it sees the
// v = 2 written after the edge, where the unstrobed one sees v = 1.
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

// §19.3 with §19.7.1: a strobed covergroup takes one sample per time slot
// however often its clocking event occurs in it, the value v holds at the end
// of the slot, while a procedural sample() call is taken at once.
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

// §19.4 with §19.7.1: an embedded covergroup's strobe option defers its
// clocking-event samples to the Postponed region as well.
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

// §19.3 with §7.4: an element of an unpacked array of a covergroup type holds
// the instance a new assigned to it builds, apart from its sibling's.
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

// §19.3 with §8.3 and §26.3: a class property whose type is a covergroup the
// module or a package declares holds the instance the constructor's new
// builds.
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

// §19.3 with §8.9: a static class property of a covergroup type holds the
// instance `K::s = new` builds.
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

// §19.3 with §6.21 and §13.4: a variable of a covergroup type declared in an
// automatic function, an automatic task or a procedural block holds the
// instance its new initializer builds.
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

// §19.3: a named fork that completes, as a block that is not disabled,
// triggers its end block event once its join is satisfied.
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

// §19.3 with §8.13: a property of a covergroup type a derived class inherits
// receives the instance a new in the derived constructor builds, and a module
// covergroup variable assigned a new in a method keeps its own.
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

// §19.3 with §8.7 and §26.3: a class property of a covergroup type a package
// declares, given `new` by its declaration, holds an instance as one given
// `new` in the constructor does, each counting the sample of 0 as 1 of 4
// bins. The initialized one held none.
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

// §19.3 with §3.12.1: a covergroup the compilation unit declares is a type
// every scope below it sees, so a module variable, a class property given
// `new` in the constructor and an automatic local of it each hold an instance
// of their own, counting 1, 2 and 3 of the 4 values. Each held none, the type
// found neither by the elaboration of the variable nor at the run.
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
