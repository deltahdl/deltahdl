#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, DerivedOverridesBaseCoverpoint) {
  CoverageDB db;
  CoverGroup* base = db.CreateGroup("base_cg");

  CoverPoint* a = CoverageDB::AddCoverPoint(base, "a");
  CoverBin a_bin;
  a_bin.name = "a0";
  a_bin.values = {0};
  a_bin.hit_count = 0;
  CoverageDB::AddBin(a, a_bin);

  CoverPoint* b = CoverageDB::AddCoverPoint(base, "b");
  CoverBin b_bin;
  b_bin.name = "b0";
  b_bin.values = {1};
  b_bin.hit_count = 1;
  CoverageDB::AddBin(b, b_bin);

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(base), 50.0);

  CoverageDB::ApplyDerivedCoverpointOverrides(base, {"a"});
  EXPECT_TRUE(base->coverpoints[0].excluded_from_coverage);
  EXPECT_FALSE(base->coverpoints[1].excluded_from_coverage);

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(base), 100.0);
}

TEST(Coverage, BaseCrossStillContributesAfterCoverpointOverride) {
  CoverageDB db;
  CoverGroup* base = db.CreateGroup("base_cg");

  CoverPoint* a = CoverageDB::AddCoverPoint(base, "a");
  CoverBin a_bin;
  a_bin.name = "a0";
  a_bin.hit_count = 0;
  CoverageDB::AddBin(a, a_bin);

  CrossCover cross;
  cross.name = "x1";
  cross.coverpoint_names = {"a"};
  CrossBin xb;
  xb.name = "xb0";
  xb.hit_count = 1;
  cross.bins.push_back(xb);
  CoverageDB::AddCross(base, cross);

  CoverageDB::ApplyDerivedCoverpointOverrides(base, {"a"});
  CoverageDB::ApplyDerivedCrossOverrides(base, {});

  EXPECT_TRUE(base->coverpoints[0].excluded_from_coverage);
  EXPECT_FALSE(base->crosses[0].excluded_from_coverage);

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(base), 100.0);
}

TEST(Coverage, DerivedCrossWithSameNameOverridesBaseCross) {
  CoverageDB db;
  CoverGroup* base = db.CreateGroup("base_cg");

  CrossCover cross;
  cross.name = "x1";
  CrossBin xb;
  xb.name = "xb0";
  xb.hit_count = 1;
  cross.bins.push_back(xb);
  CoverageDB::AddCross(base, cross);

  CoverageDB::ApplyDerivedCrossOverrides(base, {"x1"});
  EXPECT_TRUE(base->crosses[0].excluded_from_coverage);
}

TEST(Coverage, DerivedAndBaseAreSeparateTypesForGetCoverage) {
  EXPECT_FALSE(CoverageDB::CovergroupTypesAggregate("base_cg", "derived_cg"));
  EXPECT_TRUE(CoverageDB::CovergroupTypesAggregate("base_cg", "base_cg"));
}

TEST(DerivedCovergroupSim, EachDerivedCovergroupAddsItsItemsToTheBases) {
  SimFixture f;
  auto out = RunCapture(
      "class a_c;\n"
      "  bit p, q, r;\n"
      "  covergroup g;\n"
      "    cp: coverpoint p;\n"
      "  endgroup\n"
      "  function new(); g = new; endfunction\n"
      "endclass\n"
      "class b_c extends a_c;\n"
      "  covergroup extends g;\n"
      "    cq: coverpoint q;\n"
      "  endgroup : g\n"
      "  function new(); super.new(); endfunction\n"
      "endclass\n"
      "class c_c extends b_c;\n"
      "  covergroup extends g;\n"
      "    cr: coverpoint r;\n"
      "  endgroup : g\n"
      "  function new(); super.new(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic a_c x = new;\n"
      "    automatic b_c y = new;\n"
      "    automatic c_c z = new;\n"
      "    int cov, t1, t2, t3;\n"
      "    void'(x.g.get_inst_coverage(cov, t1));\n"
      "    void'(y.g.get_inst_coverage(cov, t2));\n"
      "    void'(z.g.get_inst_coverage(cov, t3));\n"
      "    $display(\"%0d %0d %0d\", t1, t2, t3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 4 6\n");
}

TEST(DerivedCovergroupSim, ABasesOptionAppliesUnlessTheDerivedOneSetsIt) {
  SimFixture f;
  auto out = RunCapture(
      "class base;\n"
      "  bit b;\n"
      "  covergroup g1;\n"
      "    option.at_least = 2;\n"
      "    cp: coverpoint b { bins one = {1}; }\n"
      "  endgroup\n"
      "  function new(); g1 = new; endfunction\n"
      "endclass\n"
      "class d1 extends base;\n"
      "  bit k;\n"
      "  covergroup extends g1;\n"
      "    ck: coverpoint k { bins z = {0}; }\n"
      "  endgroup : g1\n"
      "  function new(); super.new(); endfunction\n"
      "endclass\n"
      "class d2 extends base;\n"
      "  covergroup extends g1;\n"
      "    option.at_least = 1;\n"
      "  endgroup : g1\n"
      "  function new(); super.new(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic d1 y = new;\n"
      "    automatic d2 z = new;\n"
      "    real first;\n"
      "    y.b = 1; y.g1.sample();\n"
      "    first = y.g1.get_inst_coverage();\n"
      "    y.g1.sample();\n"
      "    z.b = 1; z.g1.sample();\n"
      "    $display(\"%0.2f %0.2f %0.2f\", first, y.g1.get_inst_coverage(),\n"
      "             z.g1.get_inst_coverage());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0.00 100.00 100.00\n");
}

TEST(DerivedCovergroupSim, ADerivedCovergroupTakesTheBasesArgumentsAndEvent) {
  SimFixture f;
  auto out = RunCapture(
      "class base;\n"
      "  int v;\n"
      "  event e;\n"
      "  bit [1:0] k;\n"
      "  covergroup g1 (int lim) @(e);\n"
      "    cp: coverpoint v { bins b[] = {[0:lim]}; }\n"
      "  endgroup\n"
      "  function new(int lim); g1 = new(lim); endfunction\n"
      "endclass\n"
      "class derived extends base;\n"
      "  covergroup extends g1;\n"
      "    ck: coverpoint k { bins z = {0}; bins o = {1}; }\n"
      "  endgroup : g1\n"
      "  function new(); super.new(4); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic derived y = new;\n"
      "    int cov, tot;\n"
      "    void'(y.g1.cp.get_inst_coverage(cov, tot));\n"
      "    y.k = 1;\n"
      "    #1 -> y.e;\n"
      "    #1 $display(\"%0d %0.2f\", tot, y.g1.ck.get_inst_coverage());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 50.00\n");
}

TEST(DerivedCovergroupSim, ACoverpointOnTheDerivingClassesPropertyHasItsWidth) {
  SimFixture f;
  auto out = RunCapture(
      "class base;\n"
      "  bit b;\n"
      "  covergroup g1;\n"
      "    cp: coverpoint b;\n"
      "  endgroup\n"
      "  function new(); g1 = new; endfunction\n"
      "endclass\n"
      "class derived extends base;\n"
      "  bit [1:0] d;\n"
      "  covergroup extends g1;\n"
      "    cd: coverpoint d;\n"
      "  endgroup : g1\n"
      "  function new(); super.new(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic derived y = new;\n"
      "    int cov, tot;\n"
      "    void'(y.g1.cd.get_inst_coverage(cov, tot));\n"
      "    $display(\"%0d\", tot);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(DerivedCovergroupSim, ADerivedCrossOverridesTheBasesCrossOfItsLabel) {
  SimFixture f;
  auto out = RunCapture(
      "class base;\n"
      "  bit a, b;\n"
      "  covergroup g0;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "  covergroup g1;\n"
      "    coverpoint a;\n"
      "    coverpoint b;\n"
      "    x: cross a, b;\n"
      "  endgroup\n"
      "  function new(); g0 = new; g1 = new; endfunction\n"
      "endclass\n"
      "class derived extends base;\n"
      "  covergroup extends g1;\n"
      "    x: cross a, b { ignore_bins one = binsof(a) intersect {1}; }\n"
      "  endgroup : g1\n"
      "  function new(); super.new(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic base p = new;\n"
      "    automatic derived q = new;\n"
      "    int cov, t1, t2;\n"
      "    void'(p.g1.get_inst_coverage(cov, t1));\n"
      "    void'(q.g1.get_inst_coverage(cov, t2));\n"
      "    $display(\"%0d %0d\", t1, t2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 6\n");
}

TEST(DerivedCovergroupSim, AFurtherSubclassSharesTheDerivedCovergroupType) {
  SimFixture f;
  auto out = RunCapture(
      "class a_c;\n"
      "  bit [1:0] p, q;\n"
      "  covergroup g;\n"
      "    cp: coverpoint p { bins b[] = {[0:1]}; }\n"
      "  endgroup\n"
      "  function new(); g = new; endfunction\n"
      "endclass\n"
      "class b_c extends a_c;\n"
      "  covergroup extends g;\n"
      "    cq: coverpoint q { bins b[] = {[0:1]}; }\n"
      "  endgroup : g\n"
      "  function new(); super.new(); endfunction\n"
      "endclass\n"
      "class c_c extends b_c;\n"
      "  function new(); super.new(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  b_c b = new;\n"
      "  c_c c = new;\n"
      "  initial begin\n"
      "    b.p = 0; b.q = 0; b.g.sample();\n"
      "    $display(\"%0.2f %0.2f\", b.g.get_coverage(), c.g.get_coverage());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "25.00 25.00\n");
}

std::string Sim(const std::string& src) {
  SimFixture f;
  const std::string kOut = RunCapture(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  return kOut;
}

TEST(DerivedCovergroupSim, ADerivedWeightOverridesAndPerInstanceIsInherited) {
  EXPECT_EQ(Sim("class base;\n"
                "  bit b;\n"
                "  covergroup g1;\n"
                "    option.weight = 10;\n"
                "    option.per_instance = 1;\n"
                "    coverpoint b;\n"
                "  endgroup\n"
                "  function new(); g1 = new; endfunction\n"
                "endclass\n"
                "class derived extends base;\n"
                "  covergroup extends g1;\n"
                "    option.weight = 3;\n"
                "  endgroup\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic base p = new;\n"
                "    automatic derived q = new;\n"
                "    $display(\"%0d %0d %0d %0d\", p.g1.option.weight,\n"
                "             p.g1.option.per_instance, q.g1.option.weight,\n"
                "             q.g1.option.per_instance);\n"
                "  end\n"
                "endmodule\n"),
            "10 1 3 1\n");
}

TEST(DerivedCovergroupSim, ATypeOptionIsOverriddenOrInherited) {
  EXPECT_EQ(Sim("class base;\n"
                "  bit b;\n"
                "  covergroup g1;\n"
                "    type_option.goal = 50;\n"
                "    type_option.weight = 7;\n"
                "    coverpoint b;\n"
                "  endgroup\n"
                "  function new(); g1 = new; endfunction\n"
                "endclass\n"
                "class derived extends base;\n"
                "  covergroup extends g1;\n"
                "    type_option.goal = 90;\n"
                "  endgroup\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic base p = new;\n"
                "    automatic derived q = new;\n"
                "    $display(\"%0d %0d %0d %0d\", p.g1.type_option.goal,\n"
                "             p.g1.type_option.weight, q.g1.type_option.goal,\n"
                "             q.g1.type_option.weight);\n"
                "  end\n"
                "endmodule\n"),
            "50 7 90 7\n");
}

TEST(DerivedCovergroupSim, TheBasesSampleFunctionSamplesTheDerivedItems) {
  EXPECT_EQ(Sim("class base;\n"
                "  covergroup g1 with function sample(bit [1:0] x);\n"
                "    cx: coverpoint x { bins z = {0}; bins o = {1}; }\n"
                "  endgroup\n"
                "  function new(); g1 = new; endfunction\n"
                "endclass\n"
                "class derived extends base;\n"
                "  bit [1:0] k;\n"
                "  covergroup extends g1;\n"
                "    ck: coverpoint k { bins z = {0}; bins o = {1}; bins t = "
                "{2}; bins h = {3}; }\n"
                "  endgroup\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic derived y = new;\n"
                "    y.k = 2; y.g1.sample(1);\n"
                "    $display(\"%0.2f %0.2f\", y.g1.cx.get_inst_coverage(),\n"
                "             y.g1.ck.get_inst_coverage());\n"
                "  end\n"
                "endmodule\n"),
            "50.00 25.00\n");
}

TEST(DerivedCovergroupSim, TheBasesBlockEventSamplesTheDerivedItems) {
  EXPECT_EQ(Sim("module t;\n"
                "  task tk; endtask\n"
                "  class base;\n"
                "    bit [1:0] v;\n"
                "    covergroup g1 @@(begin tk);\n"
                "      cp: coverpoint v { bins z = {0}; bins o = {1}; }\n"
                "    endgroup\n"
                "    function new(); g1 = new; endfunction\n"
                "  endclass\n"
                "  class derived extends base;\n"
                "    bit [1:0] k;\n"
                "    covergroup extends g1;\n"
                "      ck: coverpoint k { bins z = {0}; bins o = {1}; bins t = "
                "{2}; bins h = {3}; }\n"
                "    endgroup\n"
                "    function new(); super.new(); endfunction\n"
                "  endclass\n"
                "  initial begin\n"
                "    automatic derived y = new;\n"
                "    y.v = 1; y.k = 3; tk();\n"
                "    $display(\"%0.2f %0.2f\", y.g1.cp.get_inst_coverage(),\n"
                "             y.g1.ck.get_inst_coverage());\n"
                "  end\n"
                "endmodule\n"),
            "50.00 25.00\n");
}

TEST(DerivedCovergroupSim,
     DISABLED_ABaseCrossKeepsTheBaseCoverpointsBinsAfterAnOverride) {
  EXPECT_EQ(Sim("class base;\n"
                "  bit [1:0] a; bit b;\n"
                "  covergroup g1;\n"
                "    cpa: coverpoint a { bins lo = {0}; bins hi = {1}; }\n"
                "    cpb: coverpoint b { bins z = {0}; }\n"
                "    x: cross cpa, cpb;\n"
                "  endgroup\n"
                "  function new(); g1 = new; endfunction\n"
                "endclass\n"
                "class derived extends base;\n"
                "  covergroup extends g1;\n"
                "    cpa: coverpoint a { bins only = {2}; }\n"
                "  endgroup : g1\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic base p = new;\n"
                "    automatic derived q = new;\n"
                "    int cov, t1, t2, x1, x2;\n"
                "    void'(p.g1.get_inst_coverage(cov, t1));\n"
                "    void'(q.g1.get_inst_coverage(cov, t2));\n"
                "    void'(p.g1.x.get_inst_coverage(cov, x1));\n"
                "    void'(q.g1.x.get_inst_coverage(cov, x2));\n"
                "    $display(\"%0d %0d %0d %0d\", t1, t2, x1, x2);\n"
                "  end\n"
                "endmodule\n"),
            "5 4 2 2\n");
}

TEST(DerivedCovergroupSim, ABaseCrossBelongsToTheDerivedCovergroupUnchanged) {
  EXPECT_EQ(Sim("class base;\n"
                "  bit [1:0] a; bit b;\n"
                "  covergroup g1;\n"
                "    cpa: coverpoint a { bins lo = {0}; bins hi = {1}; }\n"
                "    cpb: coverpoint b { bins z = {0}; }\n"
                "    x: cross cpa, cpb;\n"
                "  endgroup\n"
                "  function new(); g1 = new; endfunction\n"
                "endclass\n"
                "class derived extends base;\n"
                "  bit d;\n"
                "  covergroup extends g1;\n"
                "    cd: coverpoint d;\n"
                "  endgroup\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic derived q = new;\n"
                "    int cov, tot, xc, xt;\n"
                "    q.a = 1; q.b = 0; q.g1.sample();\n"
                "    void'(q.g1.get_inst_coverage(cov, tot));\n"
                "    void'(q.g1.x.get_inst_coverage(xc, xt));\n"
                "    $display(\"%0d %0d %0d %0d\", cov, tot, xc, xt);\n"
                "  end\n"
                "endmodule\n"),
            "4 7 1 2\n");
}

const char* const kOverriddenBase =
    "class base;\n"
    "  bit [1:0] a; bit b;\n"
    "  covergroup g1;\n"
    "    cpl: coverpoint a { bins lo = {0}; bins hi = {1}; }\n"
    "    coverpoint b;\n"
    "  endgroup\n"
    "  function new(); g1 = new; endfunction\n"
    "endclass\n";

TEST(DerivedCovergroupSim, ADerivedCoverpointOfALabelOverridesTheBases) {
  EXPECT_EQ(Sim(std::string(kOverriddenBase) +
                "class derived extends base;\n"
                "  covergroup extends g1;\n"
                "    cpl: coverpoint a { bins only = {2}; }\n"
                "  endgroup\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic derived q = new;\n"
                "    int cov, tot;\n"
                "    q.a = 2; q.b = 0; q.g1.sample();\n"
                "    void'(q.g1.get_inst_coverage(cov, tot));\n"
                "    $display(\"%0d %0d\", cov, tot);\n"
                "  end\n"
                "endmodule\n"),
            "2 3\n");
}

TEST(DerivedCovergroupSim,
     ADerivedCoverpointOfAnImplicitNameOverridesTheBases) {
  EXPECT_EQ(Sim(std::string(kOverriddenBase) +
                "class derived extends base;\n"
                "  covergroup extends g1;\n"
                "    b: coverpoint b { bins one = {1}; }\n"
                "  endgroup\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic derived q = new;\n"
                "    int cov, tot;\n"
                "    q.a = 0; q.b = 1; q.g1.sample();\n"
                "    void'(q.g1.get_inst_coverage(cov, tot));\n"
                "    $display(\"%0d %0d\", cov, tot);\n"
                "  end\n"
                "endmodule\n"),
            "2 3\n");
}

TEST(DerivedCovergroupSim, AnInheritedFormalBoundsTheDerivedCovergroupsBins) {
  EXPECT_EQ(Sim("class base;\n"
                "  bit a;\n"
                "  covergroup g1 (int lim);\n"
                "    cp: coverpoint a;\n"
                "  endgroup\n"
                "  function new(int l); g1 = new(l); endfunction\n"
                "endclass\n"
                "class derived extends base;\n"
                "  bit [3:0] d;\n"
                "  covergroup extends g1;\n"
                "    cd: coverpoint d { bins b[] = {[0:lim]}; }\n"
                "  endgroup\n"
                "  function new(); super.new(3); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic derived q = new;\n"
                "    int cov, tot;\n"
                "    void'(q.g1.cd.get_inst_coverage(cov, tot));\n"
                "    $display(\"%0d\", tot);\n"
                "  end\n"
                "endmodule\n"),
            "4\n");
}

TEST(DerivedCovergroupSim, ABaseMethodAndABaseHandleReachTheDerivedInstance) {
  EXPECT_EQ(Sim("class base;\n"
                "  bit p;\n"
                "  covergroup g;\n"
                "    cp: coverpoint p;\n"
                "  endgroup\n"
                "  function new(); g = new; endfunction\n"
                "  function int bins_seen();\n"
                "    int cov, tot;\n"
                "    void'(g.get_inst_coverage(cov, tot));\n"
                "    return tot;\n"
                "  endfunction\n"
                "endclass\n"
                "class derived extends base;\n"
                "  bit q;\n"
                "  covergroup extends g;\n"
                "    cq: coverpoint q;\n"
                "  endgroup\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic derived y = new;\n"
                "    automatic base h = y;\n"
                "    int cov, tot;\n"
                "    void'(h.g.get_inst_coverage(cov, tot));\n"
                "    $display(\"%0d %0d\", y.bins_seen(), tot);\n"
                "  end\n"
                "endmodule\n"),
            "4 4\n");
}

TEST(DerivedCovergroupSim, BaseAndDerivedInstancesAreNotAggregated) {
  EXPECT_EQ(Sim("class a_c;\n"
                "  bit [1:0] p;\n"
                "  covergroup g;\n"
                "    cp: coverpoint p { bins z = {0}; bins o = {1}; }\n"
                "  endgroup\n"
                "  function new(); g = new; endfunction\n"
                "endclass\n"
                "class b_c extends a_c;\n"
                "  bit [1:0] q;\n"
                "  covergroup extends g;\n"
                "    cq: coverpoint q { bins z = {0}; bins o = {1}; }\n"
                "  endgroup\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic a_c a = new;\n"
                "    automatic b_c b = new;\n"
                "    a.p = 0; a.g.sample();\n"
                "    $display(\"%0.2f %0.2f\", a.g.get_coverage(), "
                "b.g.get_coverage());\n"
                "  end\n"
                "endmodule\n"),
            "50.00 0.00\n");
}

TEST(DerivedCovergroupSim, ACrossOfANewAndAnInheritedCoverpointCountsBoth) {
  EXPECT_EQ(Sim("class base;\n"
                "  bit [1:0] a;\n"
                "  covergroup g1;\n"
                "    coverpoint a;\n"
                "  endgroup\n"
                "  function new(); g1 = new; endfunction\n"
                "endclass\n"
                "class derived extends base;\n"
                "  bit [1:0] d;\n"
                "  covergroup extends g1;\n"
                "    coverpoint d;\n"
                "    ad: cross a, d;\n"
                "  endgroup\n"
                "  function new(); super.new(); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  initial begin\n"
                "    automatic derived q = new;\n"
                "    int cov, tot;\n"
                "    q.a = 0; q.d = 0; q.g1.sample();\n"
                "    q.a = 1; q.d = 2; q.g1.sample();\n"
                "    q.a = 3; q.d = 3; q.g1.sample();\n"
                "    q.a = 0; q.d = 0; q.g1.sample();\n"
                "    void'(q.g1.ad.get_inst_coverage(cov, tot));\n"
                "    $display(\"%0d %0d\", cov, tot);\n"
                "  end\n"
                "endmodule\n"),
            "3 16\n");
}

}  // namespace
