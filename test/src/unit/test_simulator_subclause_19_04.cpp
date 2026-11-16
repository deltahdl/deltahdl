#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, CoverGroupAsClassMember) {
  struct MyClass {
    CoverageDB db;
    CoverGroup* cg = nullptr;
    void Init() { cg = db.CreateGroup("cg_in_class"); }
  };
  MyClass obj;
  obj.Init();
  ASSERT_NE(obj.cg, nullptr);
  EXPECT_EQ(obj.cg->name, "cg_in_class");
}

TEST(Coverage, UninstantiatedCoverGroupNotCreated) {
  struct MyClass {
    CoverageDB db;
    CoverGroup* cg = nullptr;
    explicit MyClass(bool instantiate) {
      if (instantiate) cg = db.CreateGroup("cg");
    }
  };

  MyClass without(false);
  EXPECT_EQ(without.cg, nullptr);
  EXPECT_EQ(without.db.GroupCount(), 0u);

  MyClass with(true);
  ASSERT_NE(with.cg, nullptr);
  EXPECT_EQ(with.db.GroupCount(), 1u);
}

TEST(CovergroupInstanceSim, EmbeddedCovergroupBuiltInConstructor) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  class xyz;\n"
                 "    bit [1:0] m_x;\n"
                 "    covergroup cov1; coverpoint m_x { bins lo = {0}; bins hi "
                 "= {3}; } endgroup\n"
                 "    function new(); cov1 = new; endfunction\n"
                 "    function void go(bit [1:0] x); m_x = x; cov1.sample(); "
                 "endfunction\n"
                 "  endclass\n"
                 "  xyz o;\n"
                 "  initial begin\n"
                 "    o = new;\n"
                 "    o.go(0);\n"
                 "    $display(\"cov=%0.2f\", o.cov1.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, EmbeddedCovergroupSamplesAtItsClockingEvent) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit clk;\n"
                 "  class xyz;\n"
                 "    bit [1:0] m_x;\n"
                 "    covergroup cov1 @(posedge clk); coverpoint m_x { bins lo "
                 "= {0}; bins hi = {3}; } endgroup\n"
                 "    function new(); cov1 = new; endfunction\n"
                 "  endclass\n"
                 "  xyz o;\n"
                 "  initial begin\n"
                 "    o = new; o.m_x = 3;\n"
                 "    #1 clk = 1; #1;\n"
                 "    $display(\"cov=%0.2f\", o.cov1.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, EmbeddedCovergroupReachedThroughThis) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  class C;\n"
                       "    bit [1:0] x;\n"
                       "    covergroup cg;\n"
                       "      coverpoint x { bins a = {1}; bins b = {2}; }\n"
                       "    endgroup\n"
                       "    function new(); cg = new; endfunction\n"
                       "    function real hit(bit [1:0] v);\n"
                       "      x = v; this.cg.sample();\n"
                       "      return this.cg.get_inst_coverage();\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  C o;\n"
                       "  initial begin\n"
                       "    o = new;\n"
                       "    $display(\"%0.2f\", o.hit(2));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

std::string ParameterizedOwner(const std::string& rest) {
  return "class C #(int N = 2);\n"
         "  bit [3:0] v;\n"
         "  covergroup cg;\n"
         "    cp: coverpoint v { bins b[] = {[0:N-1]}; }\n"
         "  endgroup\n"
         "  function new; cg = new; endfunction\n"
         "endclass\n" +
         rest;
}

TEST(EmbeddedCovergroupSim,
     EachClassSpecializationEmbedsACovergroupTypeOfItsOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(ParameterizedOwner(
                           "module t;\n"
                           "  C #(2) a1 = new;\n"
                           "  C #(2) a2 = new;\n"
                           "  C #(4) b = new;\n"
                           "  initial begin\n"
                           "    a1.v = 0; a1.cg.sample();\n"
                           "    a2.v = 1; a2.cg.sample();\n"
                           "    b.v = 2; b.cg.sample();\n"
                           "    $display(\"%0.2f %0.2f %0.2f %0.2f\", "
                           "a1.cg.get_coverage(), b.cg.get_coverage(), "
                           "a1.cg.cp.get_coverage(), b.cg.cp.get_coverage());\n"
                           "  end\n"
                           "endmodule\n"),
                       f),
            "50.00 25.00 50.00 25.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(EmbeddedCovergroupSim,
     ADerivedClassSharesItsBaseSpecializationsCovergroup) {
  SimFixture f;
  EXPECT_EQ(RunCapture(ParameterizedOwner(
                           "class D extends C #(2);\n"
                           "endclass\n"
                           "module t;\n"
                           "  C #(2) a = new;\n"
                           "  D d = new;\n"
                           "  initial begin\n"
                           "    a.v = 0; a.cg.sample();\n"
                           "    $display(\"%0.2f %0.2f\", a.cg.get_coverage(), "
                           "d.cg.get_coverage());\n"
                           "  end\n"
                           "endmodule\n"),
                       f),
            "25.00 25.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(Coverage, DISABLED_EmbeddedCovergroupVariableHoldsTheInstanceNewMade) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "covergroup cg_t; endgroup\n"
      "class C;\n"
      "  int v;\n"
      "  covergroup cg; coverpoint v; endgroup\n"
      "  function new(); cg = new; endfunction\n"
      "  function int inside_null(); return cg == null; endfunction\n"
      "endclass\n"
      "class E; int v; covergroup cg; coverpoint v; endgroup endclass\n"
      "module t;\n"
      "  C a = new;\n"
      "  E e = new;\n"
      "  cg_t m = new;\n"
      "  int r1, r2, r3, r4, r5;\n"
      "  initial begin\n"
      "    r1 = a.cg == null; r2 = a.cg != null; r3 = a.inside_null();\n"
      "    r4 = e.cg == null; r5 = m == null;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design, {{"r1", 0u}, {"r2", 1u}, {"r3", 0u}, {"r4", 1u}, {"r5", 0u}});
}

std::string RunSv(const std::string& src) {
  SimFixture f;
  const std::string kOut = RunCapture(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  return kOut;
}

TEST(Coverage, AnUncreatedEmbeddedCovergroupStaysNull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "covergroup cg_t; endgroup\n"
      "class E; int v; covergroup cg; coverpoint v; endgroup endclass\n"
      "module t;\n"
      "  E e = new;\n"
      "  cg_t m = new;\n"
      "  int r4, r5;\n"
      "  initial begin r4 = e.cg == null; r5 = m == null; end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r4", 1u}, {"r5", 0u}});
}

TEST(EmbeddedCovergroupSim, AnUncreatedCovergroupSamplesNothingAtItsEvent) {
  EXPECT_EQ(RunSv("module top;\n"
                  "  bit clk;\n"
                  "  class C;\n"
                  "    bit [1:0] v;\n"
                  "    covergroup cg @(posedge clk); coverpoint v; endgroup\n"
                  "  endclass\n"
                  "  class D;\n"
                  "    bit [1:0] v;\n"
                  "    covergroup cg @(posedge clk); coverpoint v; endgroup\n"
                  "    function new(); cg = new; endfunction\n"
                  "  endclass\n"
                  "  C c = new;\n"
                  "  D d = new;\n"
                  "  initial begin\n"
                  "    #1 clk = 1; #1 clk = 0; d.v = 2; #1 clk = 1; #1;\n"
                  "    $display(\"%0d %0.2f\", c.cg == null, "
                  "d.cg.get_inst_coverage());\n"
                  "  end\n"
                  "endmodule\n"),
            "1 50.00\n");
}

const char* const kAtLeast =
    "class C1;\n"
    "  bit [1:0] x;\n"
    "  bit clk;\n"
    "  covergroup cv (int arg, ref bit clk) @(posedge clk);\n"
    "    option.at_least = arg;\n"
    "    coverpoint x { bins one = {1}; bins two = {2}; }\n"
    "  endgroup\n"
    "  function new(int p1); cv = new(p1, clk); endfunction\n"
    "  task hit(int n);\n"
    "    repeat (n) begin #1 clk = 1; #1 clk = 0; end\n"
    "  endtask\n"
    "endclass\n";

TEST(EmbeddedCovergroupSim, AConstructorArgumentSetsAtLeast) {
  EXPECT_EQ(RunSv(std::string(kAtLeast) +
                  "module top;\n"
                  "  initial begin\n"
                  "    static C1 a = new(4);\n"
                  "    static C1 b = new(2);\n"
                  "    a.x = 1; b.x = 1;\n"
                  "    fork a.hit(3); b.hit(3); join\n"
                  "    $display(\"%0.2f %0.2f\", a.cv.get_inst_coverage(),\n"
                  "             b.cv.get_inst_coverage());\n"
                  "    a.hit(1);\n"
                  "    $display(\"%0.2f\", a.cv.get_inst_coverage());\n"
                  "  end\n"
                  "endmodule\n"),
            "0.00 50.00\n50.00\n");
}

TEST(EmbeddedCovergroupSim, AnEmbeddedCovergroupInAPackageClassSamples) {
  EXPECT_EQ(RunSv("package p;\n"
                  "  class C;\n"
                  "    bit [1:0] v;\n"
                  "    covergroup cg; coverpoint v { bins b[] = {[0:3]}; } "
                  "endgroup\n"
                  "    function new(); cg = new; endfunction\n"
                  "  endclass\n"
                  "endpackage\n"
                  "module top;\n"
                  "  initial begin\n"
                  "    static p::C o = new;\n"
                  "    o.v = 1; o.cg.sample(); o.v = 3; o.cg.sample();\n"
                  "    $display(\"%0.2f\", o.cg.get_inst_coverage());\n"
                  "  end\n"
                  "endmodule\n"),
            "50.00\n");
}

TEST(EmbeddedCovergroupSim, ALocalPropertyIsSampledAndSetsAnOption) {
  EXPECT_EQ(RunSv("class C;\n"
                  "  local bit [1:0] m_z;\n"
                  "  local int lim = 3;\n"
                  "  covergroup cg;\n"
                  "    option.at_least = lim;\n"
                  "    coverpoint m_z { bins b[] = {[0:3]}; }\n"
                  "  endgroup\n"
                  "  function new(); cg = new; endfunction\n"
                  "  function void put(bit [1:0] z); m_z = z; cg.sample(); "
                  "endfunction\n"
                  "endclass\n"
                  "module top;\n"
                  "  initial begin\n"
                  "    static C o = new;\n"
                  "    o.put(1); o.put(2); o.put(2); o.put(2); o.put(1);\n"
                  "    $display(\"%0.2f\", o.cg.get_inst_coverage());\n"
                  "  end\n"
                  "endmodule\n"),
            "25.00\n");
}

TEST(EmbeddedCovergroupSim, LocalAndProtectedPropertiesFormACross) {
  EXPECT_EQ(RunSv("class C;\n"
                  "  local bit m_a;\n"
                  "  protected bit m_b;\n"
                  "  covergroup cg;\n"
                  "    a: coverpoint m_a;\n"
                  "    b: coverpoint m_b;\n"
                  "    ab: cross a, b;\n"
                  "    xy: cross m_a, m_b;\n"
                  "  endgroup\n"
                  "  function new(); cg = new; endfunction\n"
                  "  function void put(bit a, bit b); m_a = a; m_b = b; "
                  "cg.sample(); endfunction\n"
                  "endclass\n"
                  "module top;\n"
                  "  initial begin\n"
                  "    static C o = new;\n"
                  "    o.put(0, 1); o.put(1, 1);\n"
                  "    $display(\"%0.2f %0.2f\", o.cg.ab.get_inst_coverage(),\n"
                  "             o.cg.xy.get_inst_coverage());\n"
                  "  end\n"
                  "endmodule\n"),
            "50.00 50.00\n");
}

TEST(EmbeddedCovergroupSim, TwoCovergroupsSampleAtTheirOwnEvents) {
  EXPECT_EQ(
      RunSv("module top;\n"
            "  class MC;\n"
            "    bit [1:0] m_x;\n"
            "    local bit [1:0] m_z;\n"
            "    bit clk;\n"
            "    event m_e;\n"
            "    covergroup cv1 @(posedge clk); coverpoint m_x { bins "
            "b[] = {[0:3]}; } endgroup\n"
            "    covergroup cv2 @m_e; coverpoint m_z { bins b[] = "
            "{[0:3]}; } endgroup\n"
            "    function new(); cv1 = new; cv2 = new; endfunction\n"
            "    function void setz(bit [1:0] z); m_z = z; endfunction\n"
            "  endclass\n"
            "  initial begin\n"
            "    static MC o = new;\n"
            "    o.m_x = 1; o.setz(1); #1 o.clk = 1;\n"
            "    #1 o.m_x = 2; o.setz(2); -> o.m_e;\n"
            "    #1 o.m_x = 3; o.setz(3); -> o.m_e;\n"
            "    #1 $display(\"%0.2f %0.2f\", o.cv1.get_inst_coverage(),\n"
            "                o.cv2.get_inst_coverage());\n"
            "  end\n"
            "endmodule\n"),
      "25.00 50.00\n");
}

TEST(EmbeddedCovergroupSim, AnEventOfAMemberObjectTriggersSampling) {
  EXPECT_EQ(RunSv("class Helper;\n"
                  "  event m_ev;\n"
                  "endclass\n"
                  "class MyClass;\n"
                  "  Helper m_obj;\n"
                  "  bit [1:0] m_a;\n"
                  "  covergroup Cov @(m_obj.m_ev);\n"
                  "    coverpoint m_a { bins b[] = {[0:3]}; }\n"
                  "  endgroup\n"
                  "  function new(); m_obj = new; Cov = new; endfunction\n"
                  "endclass\n"
                  "module top;\n"
                  "  initial begin\n"
                  "    static MyClass o = new;\n"
                  "    o.m_a = 1; #1 -> o.m_obj.m_ev;\n"
                  "    #1 o.m_a = 2; -> o.m_obj.m_ev;\n"
                  "    #1 o.m_a = 3;\n"
                  "    #1 $display(\"%0.2f\", o.Cov.get_inst_coverage());\n"
                  "  end\n"
                  "endmodule\n"),
            "50.00\n");
}

}  // namespace
