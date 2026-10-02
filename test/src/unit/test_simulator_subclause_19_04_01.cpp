#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

// §19.4.1: when a derived covergroup defines a coverpoint whose name matches a
// base coverpoint, that base coverpoint no longer contributes to the coverage
// computation. Here the base covergroup has an uncovered coverpoint "a" and a
// covered coverpoint "b" (50% before). Overriding "a" drops it from the
// average, leaving only "b" — coverage becomes 100%.
TEST(Coverage, DerivedOverridesBaseCoverpoint) {
  CoverageDB db;
  CoverGroup* base = db.CreateGroup("base_cg");

  CoverPoint* a = CoverageDB::AddCoverPoint(base, "a");
  CoverBin a_bin;
  a_bin.name = "a0";
  a_bin.values = {0};   // §19.5: a coverpoint bin holds a value set
  a_bin.hit_count = 0;  // uncovered
  CoverageDB::AddBin(a, a_bin);

  CoverPoint* b = CoverageDB::AddCoverPoint(base, "b");
  CoverBin b_bin;
  b_bin.name = "b0";
  b_bin.values = {1};   // §19.5: a coverpoint bin holds a value set
  b_bin.hit_count = 1;  // covered
  CoverageDB::AddBin(b, b_bin);

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(base), 50.0);

  CoverageDB::ApplyDerivedCoverpointOverrides(base, {"a"});
  EXPECT_TRUE(base->coverpoints[0].excluded_from_coverage);
  EXPECT_FALSE(base->coverpoints[1].excluded_from_coverage);

  // The overridden coverpoint no longer contributes; only "b" remains.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(base), 100.0);
}

// §19.4.1: even when a base coverpoint no longer contributes, a cross in the
// base covergroup that includes that coverpoint still contributes to the
// computation, provided the derived covergroup does not define a cross with the
// same name. Overriding coverpoint "a" excludes it, but base cross "x1" keeps
// contributing.
TEST(Coverage, BaseCrossStillContributesAfterCoverpointOverride) {
  CoverageDB db;
  CoverGroup* base = db.CreateGroup("base_cg");

  CoverPoint* a = CoverageDB::AddCoverPoint(base, "a");
  CoverBin a_bin;
  a_bin.name = "a0";
  a_bin.hit_count = 0;  // uncovered
  CoverageDB::AddBin(a, a_bin);

  CrossCover cross;
  cross.name = "x1";
  cross.coverpoint_names = {"a"};
  CrossBin xb;
  xb.name = "xb0";
  xb.hit_count = 1;  // covered
  cross.bins.push_back(xb);
  CoverageDB::AddCross(base, cross);

  CoverageDB::ApplyDerivedCoverpointOverrides(base, {"a"});
  CoverageDB::ApplyDerivedCrossOverrides(base, /*derived_cross_names=*/{});

  EXPECT_TRUE(base->coverpoints[0].excluded_from_coverage);
  EXPECT_FALSE(base->crosses[0].excluded_from_coverage);

  // The overridden coverpoint is gone, but the base cross still contributes.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(base), 100.0);
}

// §19.4.1: a base cross stops contributing when, and only when, the derived
// covergroup defines a cross with the same name.
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

  CoverageDB::ApplyDerivedCrossOverrides(base, /*derived_cross_names=*/{"x1"});
  EXPECT_TRUE(base->crosses[0].excluded_from_coverage);
}

// §19.4.1: for get_coverage(), a derived covergroup and its base covergroup are
// separate types, so no aggregation occurs across them. Only instances naming
// the same covergroup type aggregate.
TEST(Coverage, DerivedAndBaseAreSeparateTypesForGetCoverage) {
  EXPECT_FALSE(CoverageDB::CovergroupTypesAggregate("base_cg", "derived_cg"));
  EXPECT_TRUE(CoverageDB::CovergroupTypesAggregate("base_cg", "base_cg"));
}

// §19.4.1: a derived covergroup holds every item of its base it does not
// override, beside its own, and may itself be extended: each class adds a
// coverpoint of two bins, so the instances hold 2, 4 and 6 bins. Built from
// its own body alone, each derived instance held 2.
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

// §19.4.1: an option the base sets applies to the derived covergroup unless
// the derived covergroup sets it too: at_least 2 inherited leaves y's one
// sample uncovered until its second, and at_least 1 set in d2 covers z's
// first. The derived instances took the default at_least of 1 and, with no
// item of their own, none of the base's.
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

// §19.4.1: a derived covergroup has its base's argument list, so new(4)
// gives the inherited cp its five bins, and its base's coverage event, so
// triggering e samples the derived ck. Neither reached the derived instance.
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

// §19.4.1 with §19.5.3: a coverpoint the derived covergroup adds on the
// deriving class's own `bit [1:0] d` has the 4 automatic bins its type gives.
// The property's type was not found and the coverpoint took 64.
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

// §19.4.1: a cross the derived covergroup declares under the label of one of
// its base's replaces that cross, here with half of a's bins ignored, while
// the coverpoints it crosses are inherited; the base class's other covergroup,
// g0, embedded before g1, leaves g1's composition alone. The base instance
// holds 2 + 2 + 4 bins and the derived one 2 + 2 + 2.
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

}  // namespace
