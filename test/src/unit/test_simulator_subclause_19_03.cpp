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

}  // namespace
