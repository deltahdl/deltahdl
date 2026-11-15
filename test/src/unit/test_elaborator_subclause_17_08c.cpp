#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

void ExpectFreeDeclarations(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : LinesHolding(src, "x_bad")) {
    EXPECT_TRUE(ReportedError(diags, "free variable", line, "17.8") ||
                ReportedError(diags,
                              "only a checker's data declaration opens "
                              "with rand",
                              line, "A.1.8"))
        << line;
  }
  for (uint32_t line : LinesHolding(src, "y_ok")) {
    EXPECT_FALSE(ErrorOnLine(diags, line)) << line;
  }
}

std::string InTop(const std::string& cu, const std::string& items) {
  std::string src = cu;
  src += "checker chk(logic clk, bit a);\n";
  src += items;
  src +=
      "endchecker\n"
      "module top;\n"
      "  logic clk;\n"
      "  bit a;\n"
      "  chk c(clk, a);\n"
      "endmodule\n";
  return src;
}

TEST(CheckerFunctionFreeDeclarations,
     DISABLED_EachFormInACheckersFunctionIsReported) {
  ExpectFreeDeclarations(InTop(
      "",
      "  function automatic bit f1(rand bit x_bad1); return 1'b0; endfunction\n"
      "  function automatic bit f2(input rand bit x_bad2); return 1'b0; "
      "endfunction\n"
      "  function automatic bit f3(output rand bit x_bad3); return 1'b0; "
      "endfunction\n"
      "  function automatic bit f4(inout rand bit x_bad4); return 1'b0; "
      "endfunction\n"
      "  function automatic bit f5(ref rand bit x_bad5); return 1'b0; "
      "endfunction\n"
      "  function automatic bit f6(const ref rand bit x_bad6); return 1'b0; "
      "endfunction\n"
      "  function automatic bit f7;\n"
      "    input rand bit x_bad7;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  function automatic bit f8;\n"
      "    output rand bit x_bad8;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  function automatic bit f9(bit v);\n"
      "    rand bit x_bad9;\n"
      "    static rand bit x_bad10;\n"
      "    automatic rand bit x_bad11;\n"
      "    begin\n"
      "      rand bit x_bad12;\n"
      "    end\n"
      "    for (rand int x_bad13 = 0; x_bad13 < 1; x_bad13++) v = !v;\n"
      "    return v;\n"
      "  endfunction\n"
      "  function automatic bit g1(input bit y_ok1); return 1'b0; "
      "endfunction\n"
      "  function automatic bit g2;\n"
      "    input bit y_ok2;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  function automatic bit g3(bit v);\n"
      "    bit y_ok3;\n"
      "    static bit y_ok4;\n"
      "    automatic bit y_ok5;\n"
      "    begin\n"
      "      bit y_ok6;\n"
      "    end\n"
      "    for (int y_ok7 = 0; y_ok7 < 1; y_ok7++) v = !v;\n"
      "    return v;\n"
      "  endfunction\n"));
}

std::string FreeFunctions(const std::string& prefix, const char* lead) {
  std::string text = lead;
  text += "function automatic bit ";
  text += prefix;
  text += "a(rand bit x_bad_";
  text += prefix;
  text += "a); return 1'b0; endfunction\n";
  text += lead;
  text += "function automatic bit ";
  text += prefix;
  text += "b(bit v);\n";
  text += lead;
  text += "  rand bit x_bad_";
  text += prefix;
  text += "b;\n";
  text += lead;
  text += "  return v;\n";
  text += lead;
  text += "endfunction\n";
  return text;
}

TEST(CheckerFunctionFreeDeclarations,
     DISABLED_AFunctionDeclaredElsewhereIsChecked) {
  std::string cu = "package pk;\n";
  cu += FreeFunctions("p", "  ");
  cu += "endpackage\n";
  cu += FreeFunctions("u", "");
  cu += "class K;\n";
  cu += "  static function bit ka(rand bit x_bad_ka); return 1'b0; ";
  cu += "endfunction\nendclass\nimport pk::*;\n";
  std::string items = "  bit z1, z2, z3, z4, z5, z6, z7;\n  if (1) begin : g\n";
  items += FreeFunctions("g", "    ");
  items += "    always_comb z1 = ga(a) | gb(a);\n  end\n";
  items += "  for (genvar k = 0; k < 1; k++) begin : h\n";
  items += FreeFunctions("h", "    ");
  items += "    always_comb z2 = ha(a) | hb(a);\n  end\n";
  items +=
      "  always_comb z3 = pk::pa(a) | pb(a);\n"
      "  always_comb z4 = ua(a) | $unit::ub(a);\n"
      "  always_comb z5 = K::ka(a);\n";
  ExpectFreeDeclarations(InTop(cu, items));
  std::string src = "module top;\n";
  src += FreeFunctions("m", "  ");
  src +=
      "  checker mc(bit a);\n"
      "    bit z;\n"
      "    always_comb z = ma(a) | mb(a);\n"
      "  endchecker\n"
      "  bit a;\n"
      "  mc u(a);\n"
      "endmodule\n";
  ExpectFreeDeclarations(src);
}

const char* const kIdentity =
    "  function automatic bit f(bit x);\n"
    "    return x;\n"
    "  endfunction\n";

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CheckerFreeActuals, AFreeActualInEachPlaceACallStandsIsAccepted) {
  ExpectAccepted(InTop("checker inner(bit p);\nendchecker\n",
                       std::string(kIdentity) +
                           "  rand bit r;\n"
                           "  bit z1, z2, z3;\n"
                           "  always_ff @(posedge clk) z1 <= f(r);\n"
                           "  always_comb z2 = f(r);\n"
                           "  always_latch if (a) z3 = f(r);\n"
                           "  a1: assert property (@(posedge clk) f(r) || 1);\n"
                           "  m1: assume property (@(posedge clk) f(r) || 1);\n"
                           "  c1: cover property (@(posedge clk) f(r));\n"
                           "  sequence s;\n"
                           "    @(posedge clk) f(r);\n"
                           "  endsequence\n"
                           "  c2: cover property (s);\n"
                           "  let l(v) = f(v);\n"
                           "  a2: assert property (@(posedge clk) l(r) || 1);\n"
                           "  inner i1(f(r));\n"
                           "  final $display(\"%b\", f(r));\n"));
}

TEST(CheckerFreeActuals, AFunctionDeclaredInEachPlaceIsAccepted) {
  std::string src = InTop(
      "package pk;\n"
      "  function automatic bit pf(bit x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  class C;\n"
      "    static function bit sf(bit x);\n"
      "      return x;\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "function automatic bit uf(bit x);\n"
      "  return x;\n"
      "endfunction\n"
      "import pk::*;\n",
      "  rand bit r;\n"
      "  bit z1, z2, z3, z4, z5, z6;\n"
      "  if (1) begin : g\n"
      "    function automatic bit gf(bit x);\n"
      "      return x;\n"
      "    endfunction\n"
      "    always_comb z1 = gf(r);\n"
      "  end\n"
      "  always_comb z2 = pk::pf(r);\n"
      "  always_comb z3 = pf(r);\n"
      "  always_comb z4 = pk::C::sf(r);\n"
      "  always_comb z5 = uf(r);\n"
      "  always_comb z6 = $unit::uf(r);\n");
  ExpectAccepted(src);
  ExpectAccepted(
      "module top;\n"
      "  function automatic bit mf(bit x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  checker mc(logic clk);\n"
      "    rand bit r;\n"
      "    bit z;\n"
      "    always_ff @(posedge clk) z <= mf(r);\n"
      "    a1: assert property (@(posedge clk) mf(r) || 1);\n"
      "  endchecker\n"
      "  logic clk;\n"
      "  mc u(clk);\n"
      "endmodule\n");
}

TEST(CheckerFreeActuals, EachKindOfFreeActualIsAccepted) {
  ExpectAccepted(InTop("",
                       "  function automatic bit [3:0] w(bit [3:0] x);\n"
                       "    return x;\n"
                       "  endfunction\n" +
                           std::string(kIdentity) +
                           "  rand bit r;\n"
                           "  rand const bit k;\n"
                           "  rand bit [7:0] rv;\n"
                           "  bit z1, z2, z3, z4;\n"
                           "  bit [3:0] z5, z6;\n"
                           "  always_comb z1 = f(r);\n"
                           "  always_comb z2 = f(k);\n"
                           "  always_comb z3 = f(r & k);\n"
                           "  always_comb z4 = f(!r);\n"
                           "  always_comb z5 = w(rv);\n"
                           "  always_comb z6 = w(rv[3:0]);\n"));
}

}  // namespace
