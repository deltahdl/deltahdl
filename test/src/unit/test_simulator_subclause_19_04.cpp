#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
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

// §19.4: an embedded covergroup is created only when the new() method assigns
// the result of new() to its variable. If that assignment is absent the
// covergroup is not created and no data is sampled. The constructor decides at
// run time whether to instantiate; without instantiation no group exists.
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

// §19.4: an embedded covergroup is instantiated by new in the enclosing
// class's constructor, one instance per object, and samples the object's
// members.
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

// §19.3 with §19.4: an embedded covergroup with a clocking event samples at
// each occurrence of the event for the object whose instance the constructor
// built: the posedge of clk samples m_x = 3 into the bin hi.
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

// §19.4 with §8.11: a method reaches its object's embedded covergroup as
// `this.cg`, sampling and reading the object's own instance.
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

// A class C parameterized by N, embedding a covergroup cg whose coverpoint cp
// has N bins over v, then `rest` with the module body that uses it.
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

// §19.4 with §8.25: each specialization of a parameterized class is a type of
// its own, and so is the covergroup it embeds, so get_coverage() of C #(2)'s
// cg averages a1's 50 and a2's 50, and that of C #(4)'s cg is b's 25, for the
// covergroup and for its coverpoint. Over all three instances both read 41.67.
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

// §19.4 with §8.25: a class derived from C #(2) inherits C #(2)'s covergroup,
// so its instance is one more of that covergroup type: a's 50 and d's 0
// average to 25.
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

}  // namespace
