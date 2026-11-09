#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_dollar_param_reports.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DollarClassParameterElaboration,
     ClassParameterHoldingDollarIsJudgedThroughEveryClassScope) {
  ElabFixture f;
  Elaborate(
      "package pk;\n"
      "  class PC;\n"
      "    localparam L = $;\n"
      "    localparam LB = 4;\n"
      "  endclass\n"
      "  function automatic int pf();\n"
      "    int pq[$];\n"
      "    return pq[PC::L];\n"
      "  endfunction\n"
      "  function automatic int pg();\n"
      "    int pq[$];\n"
      "    return pq[PC::LB];\n"
      "  endfunction\n"
      "endpackage\n"
      "class UL;\n"
      "  localparam L = $;\n"
      "  localparam LB = 4;\n"
      "endclass\n"
      "function automatic int uf();\n"
      "  int uq[$];\n"
      "  return uq[UL::L];\n"
      "endfunction\n"
      "function automatic int ug();\n"
      "  int uq[$];\n"
      "  return uq[UL::LB];\n"
      "endfunction\n"
      "module top(input logic clk);\n"
      "  class MC;\n"
      "    localparam L = $;\n"
      "    class NC;\n"
      "      localparam L = $;\n"
      "      localparam LB = 4;\n"
      "    endclass\n"
      "  endclass\n"
      "  int q[$];\n"
      "  int v;\n"
      "  logic a;\n"
      "  sequence sop(x, m); x ##1 (x == m); endsequence\n"
      "  a1: assert property (@(posedge clk) sop(a, MC::L));\n"
      "  a2: assert property (@(posedge clk) sop(a, MC::NC::LB));\n"
      "  initial begin\n"
      "    v = q[MC::L];\n"
      "    v = q[MC::NC::L];\n"
      "    v = q[MC::NC::LB];\n"
      "    v = q[pk::PC::L];\n"
      "    v = q[pk::PC::LB];\n"
      "    v = q[$unit::UL::L];\n"
      "    v = q[$unit::UL::LB];\n"
      "    if ($isunbounded(MC::L)) v = 0; else v = q[MC::L];\n"
      "    v = q[UL::L] + q[$unit::UL::LB];\n"
      "  end\n"
      "  if (1) begin : gb\n"
      "    class GC;\n"
      "      localparam L = $;\n"
      "      localparam LB = 4;\n"
      "    endclass\n"
      "    initial v = q[GC::L];\n"
      "    initial v = q[GC::LB];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {8, 21, 39, 42, 43, 45, 47, 50, 57},
                                  {12, 25, 40, 44, 46, 48, 49, 58});
}

TEST(DollarClassParameterElaboration,
     SpecializationDecidesWhetherAClassParameterHoldsDollar) {
  ElabFixture f;
  Elaborate(
      "package pk;\n"
      "  parameter K = $;\n"
      "  class PU #(int P = $);\n"
      "  endclass\n"
      "endpackage\n"
      "class UC #(int P = $, int R = 4);\n"
      "  localparam L = P;\n"
      "endclass\n"
      "class ND #(int p);\n"
      "endclass\n"
      "module top;\n"
      "  parameter PD = $;\n"
      "  parameter PB = 4;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = q[UC#()::P];\n"
      "    v = q[UC#()::L];\n"
      "    v = q[UC#()::R];\n"
      "    v = q[UC#(4)::P];\n"
      "    v = q[UC#(4)::L];\n"
      "    v = q[UC#(.P(4))::L];\n"
      "    v = q[UC#(.R(4))::L];\n"
      "    v = q[UC#($)::P];\n"
      "    v = q[UC#(pk::K)::L];\n"
      "    v = q[UC#(5, 5)::L];\n"
      "    v = q[$unit::UC#()::L];\n"
      "    v = q[$unit::UC#(4)::L];\n"
      "    v = q[pk::PU#()::P];\n"
      "    v = q[pk::PU#(4)::P];\n"
      "    v = q[ND#(4)::p];\n"
      "    v = q[ND#($)::p];\n"
      "    v = q[UC#(PD)::L];\n"
      "    v = q[UC#(PB)::L];\n"
      "    v = q[UC#(PD - 1)::L];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {17, 18, 23, 24, 25, 27, 29, 32, 33, 35},
                                  {19, 20, 21, 22, 26, 28, 30, 31, 34});
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "parameter 'L' holds '$'", 25,
                            "6.20.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "parameter 'K' holds '$'",
                             25, "6.20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "parameter 'PD' holds '$'",
                            35, "6.20.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "parameter 'L' holds '$'",
                             35, "6.20.7"));
}

TEST(DollarClassParameterElaboration,
     TypedefsAndBaseClassesCarryTheirSpecialization) {
  ElabFixture f;
  Elaborate(
      "package pk;\n"
      "  class PC;\n"
      "    localparam L = $;\n"
      "    localparam LB = 4;\n"
      "  endclass\n"
      "endpackage\n"
      "class UC #(int P = $, int R = 4);\n"
      "  localparam L = P;\n"
      "endclass\n"
      "class BD;\n"
      "  localparam L = $;\n"
      "  localparam M = 4;\n"
      "endclass\n"
      "class SD extends BD;\n"
      "  localparam L = 4;\n"
      "  int sq[$];\n"
      "  function int f(); return sq[L]; endfunction\n"
      "  function int g(); return sq[M]; endfunction\n"
      "endclass\n"
      "class DP extends pk::PC;\n"
      "endclass\n"
      "class BN;\n"
      "  class NN;\n"
      "    localparam L = $;\n"
      "    localparam LB = 4;\n"
      "  endclass\n"
      "  typedef UC #() U;\n"
      "  typedef UC #(4) U4;\n"
      "endclass\n"
      "class DN extends BN;\n"
      "endclass\n"
      "class DN2 extends DN;\n"
      "endclass\n"
      "module top;\n"
      "  class DC extends UC;\n"
      "    int dq[$];\n"
      "    function int f(); return dq[P]; endfunction\n"
      "    function int g(); return dq[R]; endfunction\n"
      "    function int h(); return dq[L]; endfunction\n"
      "  endclass\n"
      "  class DB extends UC #(4);\n"
      "    int dq[$];\n"
      "    function int f(); return dq[P]; endfunction\n"
      "  endclass\n"
      "  typedef UC #() TD;\n"
      "  typedef UC #(4) T4;\n"
      "  typedef TD TT;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = q[TD::P];\n"
      "    v = q[T4::P];\n"
      "    v = q[TT::L];\n"
      "    v = q[DC::P];\n"
      "    v = q[DB::P];\n"
      "    v = q[SD::L];\n"
      "    v = q[SD::M];\n"
      "    v = q[DP::L];\n"
      "    v = q[DP::LB];\n"
      "    v = q[DN::NN::L];\n"
      "    v = q[DN::NN::LB];\n"
      "    v = q[DN2::NN::L];\n"
      "    v = q[DN2::NN::LB];\n"
      "    v = q[BN::U::L];\n"
      "    v = q[BN::U4::L];\n"
      "    v = q[DN2::U::L];\n"
      "    v = q[DN2::U4::L];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(
      f, {37, 39, 51, 53, 54, 58, 60, 62, 64, 66},
      {17, 18, 38, 43, 52, 55, 56, 57, 59, 61, 63, 65, 67});
}

TEST(DollarClassParameterElaboration, ImportedClassNamesItsPackagesClass) {
  ElabFixture f;
  Elaborate(
      "package pk;\n"
      "  parameter K = $;\n"
      "  parameter KB = 4;\n"
      "  class PC;\n"
      "    localparam L = $;\n"
      "    localparam LB = 4;\n"
      "  endclass\n"
      "  class PU #(int P = $);\n"
      "  endclass\n"
      "endpackage\n"
      "package pq;\n"
      "  parameter K = 4;\n"
      "  class PC;\n"
      "    localparam L = 4;\n"
      "  endclass\n"
      "endpackage\n"
      "module mimp;\n"
      "  import pk::PC;\n"
      "  import pk::K;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial v = q[PC::L];\n"
      "  initial v = q[PC::LB];\n"
      "  initial v = q[K];\n"
      "endmodule\n"
      "module mwild;\n"
      "  import pk::*;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial v = q[PC::L];\n"
      "  initial v = q[PU#(4)::P];\n"
      "  initial v = q[PU#()::P];\n"
      "  initial v = q[KB];\n"
      "endmodule\n"
      "module mother;\n"
      "  import pq::*;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial v = q[PC::L];\n"
      "  initial v = q[K];\n"
      "endmodule\n"
      "module top;\n"
      "  mimp a();\n"
      "  mwild b();\n"
      "  mother c();\n"
      "endmodule\n",
      f, "top");
  ExpectDollarParamReportedOnlyOn(f, {22, 24, 30, 32}, {23, 31, 33, 39, 40});
}

TEST(DollarClassParameterElaboration,
     ClassTypeParameterNamesTheClassItsDefaultOrSpecializationBinds) {
  ElabFixture f;
  Elaborate(
      "class UL;\n"
      "  localparam L = $;\n"
      "endclass\n"
      "class UC #(int P = $);\n"
      "  localparam L = P;\n"
      "endclass\n"
      "class W #(type T = UL);\n"
      "  int wq[$];\n"
      "  function int f(); return wq[T::L]; endfunction\n"
      "endclass\n"
      "class WB #(type T = UC #(4));\n"
      "  int wq[$];\n"
      "  function int f(); return wq[T::L]; endfunction\n"
      "endclass\n"
      "module top;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = q[W#()::T::L];\n"
      "    v = q[W#(UC#(4))::T::L];\n"
      "    v = q[W#(UC)::T::L];\n"
      "    v = q[W#(.T(UC#(4)))::T::L];\n"
      "    v = q[WB#()::T::L];\n"
      "    v = q[WB#(UL)::T::L];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {9, 19, 21, 24}, {13, 20, 22, 23});
}

TEST(DollarClassParameterElaboration,
     ModuleTypeParameterNamesTheClassEachInstanceBinds) {
  constexpr const char* kModules =
      "class UL;\n"
      "  localparam L = $;\n"
      "endclass\n"
      "class UC #(int P = $);\n"
      "  localparam L = P;\n"
      "endclass\n"
      "module mt #(type T = UL);\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial v = q[T::L];\n"
      "endmodule\n";
  ElabFixture by_default;
  Elaborate(std::string(kModules) + "module top;\n  mt u();\nendmodule\n",
            by_default, "top");
  ExpectDollarParamReportedOnlyOn(by_default, {10}, {});
  ElabFixture bounded;
  Elaborate(std::string(kModules) +
                "module top;\n  mt #(.T(UC #(4))) u();\nendmodule\n",
            bounded, "top");
  ExpectDollarParamReportedOnlyOn(bounded, {}, {10});
  ElabFixture unbounded;
  Elaborate(std::string(kModules) + "module top;\n  mt #(UC) u();\nendmodule\n",
            unbounded, "top");
  ExpectDollarParamReportedOnlyOn(unbounded, {10}, {});
}

TEST(DollarClassParameterElaboration,
     TypeParameterDeclaredAsAnItemNamesTheClassItBinds) {
  ElabFixture f;
  Elaborate(
      "package pk;\n"
      "  class PC #(int P = $);\n"
      "    localparam L = $;\n"
      "    localparam LB = 4;\n"
      "  endclass\n"
      "  parameter type PT = PC;\n"
      "  localparam type P4 = PC #(4);\n"
      "  function automatic int pf();\n"
      "    int pq[$];\n"
      "    int v;\n"
      "    v = pq[PT::L];\n"
      "    v = pq[PT::LB];\n"
      "    v = pq[PT::P];\n"
      "    return pq[P4::P];\n"
      "  endfunction\n"
      "endpackage\n"
      "class UL;\n"
      "  localparam L = $;\n"
      "  localparam LB = 4;\n"
      "endclass\n"
      "localparam type UT = UL;\n"
      "function automatic int uf();\n"
      "  int uq[$];\n"
      "  int v;\n"
      "  v = uq[UT::L];\n"
      "  return uq[UT::LB];\n"
      "endfunction\n"
      "module top;\n"
      "  localparam type MT = UL;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = q[pk::PT::L];\n"
      "    v = q[pk::PT::LB];\n"
      "    v = q[pk::P4::P];\n"
      "    v = q[UT::L];\n"
      "    v = q[$unit::UT::L];\n"
      "    v = q[$unit::UT::LB];\n"
      "    v = q[MT::L];\n"
      "    v = q[MT::LB];\n"
      "  end\n"
      "  if (1) begin : gb\n"
      "    localparam type GT = UL;\n"
      "    initial v = q[GT::L];\n"
      "    initial v = q[GT::LB];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {11, 13, 25, 33, 36, 37, 39, 44},
                                  {12, 14, 26, 34, 35, 38, 40, 45});
}

TEST(DollarClassParameterElaboration,
     ClassBodyTypeParameterNamesTheClassItBinds) {
  ElabFixture f;
  Elaborate(
      "class UL;\n"
      "  localparam L = $;\n"
      "  localparam LB = 4;\n"
      "endclass\n"
      "class W;\n"
      "  parameter type T = UL;\n"
      "  int wq[$];\n"
      "  function int f(); return wq[T::L]; endfunction\n"
      "  function int g(); return wq[T::LB]; endfunction\n"
      "endclass\n"
      "class WP #(int N = 1);\n"
      "  parameter type T = UL;\n"
      "  int wq[$];\n"
      "  function int f(); return wq[T::L]; endfunction\n"
      "  function int g(); return wq[T::LB]; endfunction\n"
      "endclass\n"
      "module top;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial v = q[W::T::L];\n"
      "  initial v = q[W::T::LB];\n"
      "  initial v = q[WP#(2)::T::L];\n"
      "  initial v = q[WP#(2)::T::LB];\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {8, 14, 20, 22}, {9, 15, 21, 23});
}

TEST(DollarClassParameterElaboration,
     ClassParameterDefinedThroughItselfEndsTheSearch) {
  ElabFixture f;
  Elaborate(
      "class S;\n"
      "  localparam L = S::L;\n"
      "endclass\n"
      "class E;\n"
      "  localparam L = $;\n"
      "endclass\n"
      "module top;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial v = q[S::L];\n"
      "  initial v = q[E::L];\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {11}, {10});
}

TEST(DollarClassParameterElaboration,
     NameThatIsNoClassParameterIsNotTakenForOne) {
  ElabFixture f;
  Elaborate(
      "typedef int qt[$];\n"
      "class MC;\n"
      "  localparam L = $;\n"
      "  int qp[$];\n"
      "  int fa[4];\n"
      "  var type(qp) w;\n"
      "  var type(qt) wt;\n"
      "  function int f(); return fa[$]; endfunction\n"
      "  function int g(); return w[$]; endfunction\n"
      "  function int h(); return wt[$]; endfunction\n"
      "endclass\n"
      "module top;\n"
      "  struct { int L; } MC2;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial v = q[MC2.L];\n"
      "  initial v = q[MC::L];\n"
      "  initial v = q[NoSuch::L];\n"
      "  initial v = q[MC::NoSuch::L];\n"
      "  initial v = q[NoSuch::Inner::L];\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {17}, {16, 18, 19, 20});
  constexpr std::string_view kLoneDollar =
      "'$' may stand only in a queue's dimension or select";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kLoneDollar, 8, "6.20.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kLoneDollar, 9, "6.20.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kLoneDollar, 10, "6.20.7"));
}

TEST(DollarClassParameterElaboration,
     ClassNamedThroughATypedefOrADeeperNestingIsFollowed) {
  ElabFixture f;
  Elaborate(
      "class MC;\n"
      "  class NC;\n"
      "    class DC;\n"
      "      localparam L = $;\n"
      "      localparam LB = 4;\n"
      "    endclass\n"
      "    localparam L = $;\n"
      "    localparam LB = 4;\n"
      "  endclass\n"
      "endclass\n"
      "typedef MC::NC TN;\n"
      "class DN extends MC::NC;\n"
      "endclass\n"
      "module top;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = q[MC::NC::DC::L];\n"
      "    v = q[MC::NC::DC::LB];\n"
      "    v = q[TN::L];\n"
      "    v = q[TN::LB];\n"
      "    v = q[TN::DC::L];\n"
      "    v = q[TN::DC::LB];\n"
      "    v = q[DN::L];\n"
      "    v = q[DN::LB];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {18, 20, 22, 24}, {19, 21, 23, 25});
}

TEST(DollarClassParameterElaboration,
     DerivedClassDeclarationHidesTheNameItsBaseDeclares) {
  ElabFixture f;
  Elaborate(
      "class BN;\n"
      "  class NN;\n"
      "    localparam L = $;\n"
      "  endclass\n"
      "  class NT;\n"
      "    localparam L = $;\n"
      "  endclass\n"
      "  class NC;\n"
      "    localparam L = $;\n"
      "  endclass\n"
      "  localparam L = $;\n"
      "endclass\n"
      "class DV extends BN;\n"
      "  int NN;\n"
      "  typedef int NT;\n"
      "  class NC;\n"
      "    localparam L = 4;\n"
      "  endclass\n"
      "endclass\n"
      "class DP #(int L = 4) extends BN;\n"
      "endclass\n"
      "class DX extends Missing;\n"
      "  localparam L = 4;\n"
      "endclass\n"
      "module top;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = q[BN::NN::L];\n"
      "    v = q[DV::NN::L];\n"
      "    v = q[BN::NT::L];\n"
      "    v = q[DV::NT::L];\n"
      "    v = q[BN::NC::L];\n"
      "    v = q[DV::NC::L];\n"
      "    v = q[DV::L];\n"
      "    v = q[DP#()::L];\n"
      "    v = q[DX::L];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {29, 31, 33, 35}, {30, 32, 34, 36, 37});
}

TEST(DollarClassParameterElaboration,
     TypedefOrBaseClassSpecializationBindsATypeParameter) {
  ElabFixture f;
  Elaborate(
      "class UL;\n"
      "  localparam L = $;\n"
      "endclass\n"
      "class UC #(int P = $);\n"
      "  localparam L = P;\n"
      "endclass\n"
      "class W #(type T = UL);\n"
      "endclass\n"
      "typedef W #(UC #(4)) WT;\n"
      "typedef W #(UC) WU;\n"
      "typedef W #(.T(UC #(4))) WN;\n"
      "class DW extends W #(UC);\n"
      "endclass\n"
      "class DB extends W #(UC #(4));\n"
      "endclass\n"
      "class LC #(int P = 4, localparam int LQ = $);\n"
      "endclass\n"
      "module top;\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = q[WT::T::L];\n"
      "    v = q[WU::T::L];\n"
      "    v = q[WN::T::L];\n"
      "    v = q[DW::T::L];\n"
      "    v = q[DB::T::L];\n"
      "    v = q[LC#(.P(5))::LQ];\n"
      "    v = q[LC#(.P(5))::P];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {23, 25, 27}, {22, 24, 26, 28});
}

}  // namespace
