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

}  // namespace
