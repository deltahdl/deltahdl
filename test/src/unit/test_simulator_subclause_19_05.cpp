#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, AddCoverPointToGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  ASSERT_NE(cp, nullptr);
  EXPECT_EQ(cp->name, "addr");
  EXPECT_EQ(g->coverpoints.size(), 1u);
}

TEST(Coverage, IffGuardBlocksSampling) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = false;

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, IffGuardAllowsSampling) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = true;

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

TEST(Coverage, ValueBinCountIncrementsOnEachMatch) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin b;
  b.name = "set";
  b.values = {0, 1, 2};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 1}});
  db.Sample(g, {{"x", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 2u);
}

TEST(Coverage, ValueBinCountUnchangedOnMiss) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin b;
  b.name = "set";
  b.values = {0, 1, 2};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 9}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, TransitionBinCountsOnSequenceMatch) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin t;
  t.name = "t01";
  t.kind = CoverBinKind::kTransition;
  t.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, t);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

TEST(Coverage, TransitionBinDoesNotCountWithoutSequence) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin t;
  t.name = "t01";
  t.kind = CoverBinKind::kTransition;
  t.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, t);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, TransitionBinCountsOnMultiStepSequence) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin t;
  t.name = "t012";
  t.kind = CoverBinKind::kTransition;
  t.transitions = {{0, 1, 2}};
  CoverageDB::AddBin(cp, t);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
  db.Sample(g, {{"x", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

TEST(Coverage, DefaultBinCatchesUnmatchedValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin defined;
  defined.name = "lo";
  defined.values = {0, 1};
  CoverageDB::AddBin(cp, defined);

  CoverBin def;
  def.name = "others";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  db.Sample(g, {{"x", 7}});
  EXPECT_EQ(g->coverpoints[0].bins[1].hit_count, 1u);
}

TEST(Coverage, DefaultBinSkipsDefinedValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin defined;
  defined.name = "lo";
  defined.values = {0, 1};
  CoverageDB::AddBin(cp, defined);

  CoverBin def;
  def.name = "others";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[1].hit_count, 0u);
}

TEST(Coverage, AutoBinMaxControlsAutoBinCount) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 4;
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_EQ(cp->bins.size(), 4u);
}

TEST(Coverage, AutoBinsAreMarkedAuto) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 4;
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_EQ(cp->bins[0].kind, CoverBinKind::kAuto);
}

TEST(Coverage, NoAutoBinsForRealCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 8;
  auto* cp = CoverageDB::AddCoverPoint(g, "r");
  cp->is_real = true;

  EXPECT_FALSE(CoverageDB::AutoBinsAllowed(cp));
  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_TRUE(cp->bins.empty());
}

TEST(Coverage, DefaultBinExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin defined;
  defined.name = "lo";
  defined.values = {0};
  CoverageDB::AddBin(cp, defined);

  CoverBin def;
  def.name = "others";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&g->coverpoints[0]), 100.0);
}

TEST(CovergroupInstanceSim, DefaultBinFromDeclarationNotCounted) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins a = {0}; bins b = {1}; bins "
                       "others = default; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 2; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=0 t=2\n");
}

TEST(CovergroupInstanceSim, CoverpointDataTypeConvertsTheSample) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [7:0] v; int n, t;\n"
          "  covergroup cg;\n"
          "    bit [1:0] lo2: coverpoint v;\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin v = 8'h05; c.sample(); void'(c.get_inst_coverage(n, "
          "t)); $display(\"n=%0d t=%0d\", n, t); end\n"
          "endmodule\n",
          f),
      "n=1 t=4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, CoverpointDataTypeWidensTheExpression) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [1:0] a, b;\n"
          "  covergroup cg;\n"
          "    bit [2:0] cp: coverpoint a + b { bins f = {4}; bins s = {5}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    a = 3; b = 1; c.sample();\n"
          "    $display(\"cov=%0.2f\", c.get_inst_coverage());\n"
          "  end\n"
          "endmodule\n",
          f),
      "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, CoverpointIffGuardIgnoresSample) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v; bit en;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v iff (en) { bins lo = {0}; bins hi = {3}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    en = 0; v = 0; c.sample();\n"
                 "    en = 1; v = 3; c.sample();\n"
                 "    $display(\"cov=%0.2f\", c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, BinsReadTheGenerateBlockGenvar) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [1:0] v = 1;\n"
          "  for (genvar g = 1; g <= 2; g++) begin : G\n"
          "    covergroup cg; coverpoint v { bins b[] = {[1:g]}; } endgroup\n"
          "    cg c = new;\n"
          "  end\n"
          "  initial begin\n"
          "    G[1].c.sample(); G[2].c.sample();\n"
          "    $display(\"%0.2f %0.2f\", G[1].c.get_inst_coverage(),\n"
          "             G[2].c.get_inst_coverage());\n"
          "  end\n"
          "endmodule\n",
          f),
      "100.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

std::string SimOk(const std::string& src) {
  SimFixture f;
  const std::string kOut = RunCapture(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  return kOut;
}

TEST(CovergroupInstanceSim, AnImplicitDataTypeConvertsTheSample) {
  EXPECT_EQ(SimOk("module top;\n"
                  "  bit [7:0] v; int n, t;\n"
                  "  covergroup cg;\n"
                  "    [1:0] lo: coverpoint v;\n"
                  "  endgroup\n"
                  "  cg c = new;\n"
                  "  initial begin\n"
                  "    v = 8'h05; c.sample();\n"
                  "    void'(c.get_inst_coverage(n, t));\n"
                  "    $display(\"n=%0d t=%0d\", n, t);\n"
                  "  end\n"
                  "endmodule\n"),
            "n=1 t=4\n");
}

TEST(CovergroupInstanceSim, AnIntDataTypeOverARealSamplesTheConvertedValue) {
  EXPECT_EQ(
      SimOk("module top;\n"
            "  real r;\n"
            "  covergroup cg;\n"
            "    int ic: coverpoint r { bins one = {1}; bins two = {2}; }\n"
            "  endgroup\n"
            "  cg c = new;\n"
            "  initial begin\n"
            "    r = 1.4; c.sample();\n"
            "    $display(\"%0.2f\", c.get_inst_coverage());\n"
            "  end\n"
            "endmodule\n"),
      "50.00\n");
}

const char* const kVif =
    "interface ifc;\n"
    "  logic [1:0] v;\n"
    "  logic en;\n"
    "endinterface\n"
    "class C;\n"
    "  virtual ifc w;\n"
    "  bit x;\n";

const char* const kVifTop =
    "module top;\n"
    "  ifc u();\n"
    "  initial begin\n"
    "    static C o = new(u);\n";

TEST(CovergroupInstanceSim, ACoverpointReadsAVirtualInterfaceMember) {
  EXPECT_EQ(SimOk(std::string(kVif) +
                  "  covergroup cg;\n"
                  "    coverpoint w.v { bins a = {1}; bins b = {3}; }\n"
                  "  endgroup\n"
                  "  function new(virtual ifc h); w = h; cg = new; "
                  "endfunction\n"
                  "endclass\n" +
                  kVifTop +
                  "    u.v = 3; o.cg.sample();\n"
                  "    $display(\"%0.2f\", o.cg.get_inst_coverage());\n"
                  "  end\n"
                  "endmodule\n"),
            "50.00\n");
}

TEST(CovergroupInstanceSim, AnIffGuardReadsAVirtualInterfaceMember) {
  EXPECT_EQ(
      SimOk(std::string(kVif) +
            "  covergroup cg;\n"
            "    coverpoint x iff (w.en) { bins z = {0}; bins o = {1}; }\n"
            "  endgroup\n"
            "  function new(virtual ifc h); w = h; cg = new; "
            "endfunction\n"
            "endclass\n" +
            kVifTop +
            "    u.en = 0; o.x = 0; o.cg.sample();\n"
            "    u.en = 1; o.x = 1; o.cg.sample();\n"
            "    $display(\"%0.2f\", o.cg.get_inst_coverage());\n"
            "  end\n"
            "endmodule\n"),
      "50.00\n");
}

std::string ClockedRun(const char* skew, const char* bin) {
  return std::string(
             "module top;\n"
             "  bit clk;\n"
             "  bit [1:0] v;\n"
             "  clocking cb @(posedge clk);\n"
             "    input ") +
         skew +
         " v;\n"
         "  endclocking\n"
         "  covergroup cg;\n"
         "    coverpoint cb.v { " +
         bin +
         " }\n"
         "  endgroup\n"
         "  cg c = new;\n"
         "  initial begin\n"
         "    v = 3;\n"
         "    #5 clk = 1; v = 2;\n"
         "    #1 c.sample();\n"
         "    $display(\"%0.2f\", c.get_inst_coverage());\n"
         "  end\n"
         "endmodule\n";
}

TEST(CovergroupInstanceSim, DISABLED_AStepSkewClockvarSamplesThePreponedValue) {
  EXPECT_EQ(SimOk(ClockedRun("#1step", "bins three = {3};")), "100.00\n");
}

TEST(CovergroupInstanceSim, DISABLED_AZeroSkewClockvarSamplesTheObservedValue) {
  EXPECT_EQ(SimOk(ClockedRun("#0", "bins two = {2};")), "100.00\n");
}

std::string BinTotals(const std::string& head,
                      const std::vector<std::string>& points) {
  std::string reads;
  for (const std::string& point : points) {
    reads += "    void'(c." + point +
             ".get_inst_coverage(n, t)); $write(\"%0d \", t);\n";
  }
  return SimOk(head +
               "  cg c = new(rr, 5);\n"
               "  initial begin\n" +
               reads +
               "    $display;\n"
               "  end\n"
               "endmodule\n");
}

TEST(InferredCoverpointTypeSim, AnOperationTakesItsSelfDeterminedType) {
  EXPECT_EQ(BinTotals("module top;\n"
                      "  typedef struct packed { bit [2:0] f; bit g; } s_t;\n"
                      "  typedef bit [2:0] t3;\n"
                      "  bit [1:0] a, b; bit [31:0] wide; bit [2:0] rr;\n"
                      "  t3 td; s_t s; bit [2:0] arr [4];\n"
                      "  bit [3:0][2:0] pa; bit [2:0] q[$]; int n, t;\n"
                      "  covergroup cg (ref bit [2:0] r, input int k);\n"
                      "    c_add: coverpoint a + b;\n"
                      "    c_cat: coverpoint {a, b};\n"
                      "    c_eq: coverpoint a == b;\n"
                      "    c_cond: coverpoint (a[0] ? a : b);\n"
                      "    c_red: coverpoint &a;\n"
                      "    c_sh: coverpoint a << 1;\n"
                      "    c_cast: coverpoint 3'(a);\n"
                      "    c_sg: coverpoint $signed(a);\n"
                      "    c_co: coverpoint $countones(a);\n"
                      "    c_qs: coverpoint q.size();\n"
                      "    c_ps: coverpoint wide[31:29];\n"
                      "    c_sl: coverpoint pa[1][1:0];\n"
                      "    c_pe: coverpoint pa[1];\n"
                      "    c_ae: coverpoint arr[1];\n"
                      "    c_sm: coverpoint s.f;\n"
                      "    c_s: coverpoint s;\n"
                      "    c_td: coverpoint td;\n"
                      "    c_ref: coverpoint r;\n"
                      "    c_in: coverpoint k;\n"
                      "  endgroup\n",
                      {"c_add", "c_cat", "c_eq", "c_cond", "c_red", "c_sh",
                       "c_cast", "c_sg", "c_co", "c_qs", "c_ps", "c_sl", "c_pe",
                       "c_ae", "c_sm", "c_s", "c_td", "c_ref", "c_in"}),
            "4 16 2 4 2 4 8 4 64 64 8 4 8 8 8 16 8 8 64 \n");
}

TEST(InferredCoverpointTypeSim, ScopedNamesAndCallsTakeTheirDeclaredType) {
  EXPECT_EQ(BinTotals("bit [2:0] uv;\n"
                      "function automatic bit [2:0] uf(input bit [1:0] x);\n"
                      "  return {1'b1, x};\n"
                      "endfunction\n"
                      "package pk;\n"
                      "  bit [2:0] pv;\n"
                      "  function automatic bit [2:0] pf(input bit [1:0] x);\n"
                      "    return {1'b1, x};\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  class K;\n"
                      "    static bit [2:0] sp;\n"
                      "    bit [2:0] hp;\n"
                      "    static function bit [2:0] sf(input bit [1:0] x);\n"
                      "      return {1'b1, x};\n"
                      "    endfunction\n"
                      "    function bit [2:0] mf(); return hp; endfunction\n"
                      "  endclass\n"
                      "  bit [1:0] a; bit [2:0] rr; int n, t;\n"
                      "  K h = new;\n"
                      "  covergroup cg (ref bit [2:0] r, input int k);\n"
                      "    c_uv: coverpoint uv;\n"
                      "    c_uf: coverpoint uf(a);\n"
                      "    c_pv: coverpoint pk::pv;\n"
                      "    c_pf: coverpoint pk::pf(a);\n"
                      "    c_sp: coverpoint K::sp;\n"
                      "    c_sf: coverpoint K::sf(a);\n"
                      "    c_hp: coverpoint h.hp;\n"
                      "    c_mf: coverpoint h.mf();\n"
                      "  endgroup\n",
                      {"c_uv", "c_uf", "c_pv", "c_pf", "c_sp", "c_sf", "c_hp",
                       "c_mf"}),
            "8 8 8 8 8 8 8 8 \n");
}

TEST(InferredCoverpointTypeSim,
     DISABLED_AHierarchicalNameOrModuleFunctionKeepsItsWidth) {
  EXPECT_EQ(
      BinTotals("interface ifc; bit [2:0] sig; endinterface\n"
                "module leaf; bit [2:0] lx; endmodule\n"
                "module mid; leaf l(); bit [2:0] sx; endmodule\n"
                "module top;\n"
                "  bit [1:0] a; bit [2:0] rr; int n, t;\n"
                "  mid u(); ifc i(); virtual ifc vif = i;\n"
                "  function automatic bit [2:0] f3(input bit [1:0] x);\n"
                "    return {1'b1, x};\n"
                "  endfunction\n"
                "  if (1) begin : gen\n"
                "    bit [2:0] gx;\n"
                "  end\n"
                "  covergroup cg (ref bit [2:0] r, input int k);\n"
                "    c_u: coverpoint u.sx;\n"
                "    c_top: coverpoint top.u.sx;\n"
                "    c_two: coverpoint u.l.lx;\n"
                "    c_ifc: coverpoint i.sig;\n"
                "    c_vif: coverpoint vif.sig;\n"
                "    c_gen: coverpoint gen.gx;\n"
                "    c_fn: coverpoint f3(a);\n"
                "  endgroup\n",
                {"c_u", "c_top", "c_two", "c_ifc", "c_vif", "c_gen", "c_fn"}),
      "8 8 8 8 8 8 8 \n");
}

TEST(InferredCoverpointTypeSim,
     DISABLED_AnInterfacePortOrScopeFunctionKeepsItsWidth) {
  EXPECT_EQ(
      SimOk(
          "interface ifc;\n"
          "  bit [2:0] sig; bit [1:0] a; int n, t;\n"
          "  function automatic bit [2:0] ifn(input bit [1:0] x);\n"
          "    return {1'b1, x};\n"
          "  endfunction\n"
          "  covergroup icg; coverpoint ifn(a); endgroup\n"
          "  icg c = new;\n"
          "  initial #1 begin\n"
          "    void'(c.get_inst_coverage(n, t)); $display(\"i %0d\", t);\n"
          "  end\n"
          "  modport mp (input sig);\n"
          "endinterface\n"
          "program pg;\n"
          "  bit [1:0] a; int n, t;\n"
          "  function automatic bit [2:0] pfn(input bit [1:0] x);\n"
          "    return {1'b1, x};\n"
          "  endfunction\n"
          "  covergroup gcg; coverpoint pfn(a); endgroup\n"
          "  gcg c = new;\n"
          "  initial #9 begin\n"
          "    void'(c.get_inst_coverage(n, t)); $display(\"p %0d\", t);\n"
          "  end\n"
          "endprogram\n"
          "module user (ifc p, ifc.mp q);\n"
          "  int n, t;\n"
          "  covergroup ucg; cp: coverpoint p.sig; cq: coverpoint q.sig;\n"
          "  endgroup\n"
          "  ucg c = new;\n"
          "  initial #3 begin\n"
          "    void'(c.cp.get_inst_coverage(n, t)); $display(\"pp %0d\", t);\n"
          "    void'(c.cq.get_inst_coverage(n, t)); $display(\"mp %0d\", t);\n"
          "  end\n"
          "endmodule\n"
          "module top;\n"
          "  bit [1:0] a;\n"
          "  ifc i(); pg g(); user us(i, i);\n"
          "  if (1) begin : gen\n"
          "    int n, t; bit [2:0] gx;\n"
          "    function automatic bit [2:0] gf(input bit [1:0] x);\n"
          "      return {1'b1, x};\n"
          "    endfunction\n"
          "    covergroup bcg; cf: coverpoint gf(a); cx: coverpoint gx;\n"
          "    endgroup\n"
          "    bcg c = new;\n"
          "    initial #4 begin\n"
          "      void'(c.cf.get_inst_coverage(n, t)); $display(\"g %0d\", t);\n"
          "      void'(c.cx.get_inst_coverage(n, t)); $display(\"x %0d\", t);\n"
          "    end\n"
          "  end\n"
          "endmodule\n"),
      "i 8\npp 8\nmp 8\ng 8\nx 8\np 8\n");
}

}  // namespace
