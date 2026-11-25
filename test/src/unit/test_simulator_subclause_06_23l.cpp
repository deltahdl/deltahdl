#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kClasses =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  logic [8:0] w9;\n"
    "  parameter logic [4:0] P5 = 3;\n"
    "  class K; int m = 5; endclass\n"
    "endpackage\n"
    "class X #(type T = int);\n"
    "  T v;\n"
    "  static int s;\n"
    "  function int w(); return $bits(v); endfunction\n"
    "endclass\n"
    "module z; logic [3:0] hv; endmodule\n";

constexpr int kFirstLine = 13;

struct Place {
  std::string_view open;
  std::string_view close;
};

constexpr Place kPlaces[] = {
    {"module top; z u();\n", "endmodule\n"},
    {"module top; z u(); d x(); endmodule\ninterface d;\n", "endinterface\n"},
    {"module top; z u(); d x(); endmodule\nprogram d;\n", "endprogram\n"},
    {"module top; z u();\n  logic [1:0] n;\n  if (1) begin : g\n",
     "  end\nendmodule\n"},
    {"module top; z u();\n  logic [1:0] n;\n"
     "  for (genvar i = 0; i < 1; i++) begin : g\n",
     "  end\nendmodule\n"},
};

void ExpectInEachPlace(std::string_view items, std::string_view printed) {
  for (const Place& place : kPlaces) {
    const std::string kSource =
        std::string(place.open).append(items).append(place.close);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(std::string(kClasses).append(kSource), f), printed);
  }
}

TEST(ClassItemTypeRefArgumentSim, SpecializesAPropertyAndALocal) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  class P;\n"
      "    X #(type(n)) a = new;\n"
      "    X #(type(logic [5:0])) b = new;\n"
      "    static X #(type(n)) c = new;\n"
      "    function int f();\n"
      "      X #(type(n)) z;\n"
      "      z = new;\n"
      "      return $bits(z.v) * 10 + $bits(a.v);\n"
      "    endfunction\n"
      "  endclass\n"
      "  P p = new;\n"
      "  initial begin\n"
      "    $display(\"%0d %0d %0d\", $bits(p.a.v), p.a.w(), p.f());\n"
      "    $display(\"%0d %0d %0d\", $bits(p.b.v), p.b.w(), P::c.w());\n"
      "  end\n",
      "7 7 77\n6 6 7\n");
}

TEST(ClassItemTypeRefArgumentSim, NamesAPropertyAFormalOrALocal) {
  ExpectInEachPlace(
      "  class P;\n"
      "    logic [4:0] k;\n"
      "    X #(type(k)) a = new;\n"
      "    function int f(logic [2:0] q);\n"
      "      logic [3:0] l;\n"
      "      X #(type(q)) x;\n"
      "      X #(.T(type(l))) y;\n"
      "      X #(type(k)) z;\n"
      "      x = new;\n"
      "      y = new;\n"
      "      z = new;\n"
      "      return x.w() * 100 + y.w() * 10 + z.w();\n"
      "    endfunction\n"
      "  endclass\n"
      "  P p = new;\n"
      "  initial $display(\"%0d %0d\", p.a.w(), p.f(0));\n",
      "5 345\n");
}

TEST(ClassItemTypeRefArgumentSim, SpecializesAFormalAndAReturnType) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  class P;\n"
      "    function int f(X #(type(n)) a); return $bits(a.v); endfunction\n"
      "    function X #(type(n)) g();\n"
      "      X #(type(n)) z;\n"
      "      z = new;\n"
      "      return z;\n"
      "    endfunction\n"
      "    task tk(X #(.T(type(n))) a);\n"
      "      $display(\"%0d\", a.w());\n"
      "    endtask\n"
      "  endclass\n"
      "  P p = new;\n"
      "  X #(logic [6:0]) x;\n"
      "  initial begin\n"
      "    x = p.g();\n"
      "    $display(\"%0d %0d\", x.w(), p.f(x));\n"
      "    p.tk(x);\n"
      "  end\n",
      "7 7\n7\n");
}

TEST(ClassItemTypeRefArgumentSim, SpecializesATypedef) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  class P;\n"
      "    typedef X #(type(n)) xt;\n"
      "    xt a = new;\n"
      "    function int f(xt z);\n"
      "      xt y;\n"
      "      y = new;\n"
      "      return y.w() * 10 + z.w();\n"
      "    endfunction\n"
      "    function xt g();\n"
      "      xt y;\n"
      "      y = new;\n"
      "      return y;\n"
      "    endfunction\n"
      "  endclass\n"
      "  class D extends P;\n"
      "    xt b = new;\n"
      "  endclass\n"
      "  D p = new;\n"
      "  P::xt e = new;\n"
      "  initial begin\n"
      "    $display(\"%0d %0d %0d\", p.a.w(), p.b.w(), p.f(e));\n"
      "    e = p.g();\n"
      "    $display(\"%0d\", e.w());\n"
      "  end\n",
      "7 7 77\n7\n");
}

TEST(ClassItemTypeRefArgumentSim, TypedefsOfTheNameInTwoClassesStayApart) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  class P; typedef X #(type(n)) xt; xt a = new; endclass\n"
      "  class Q; typedef X #(logic [3:0]) xt; xt a = new; endclass\n"
      "  class R; typedef X #() xt; xt a = new; endclass\n"
      "  P p = new;\n"
      "  Q q = new;\n"
      "  R r = new;\n"
      "  initial $display(\"%0d %0d %0d\", p.a.w(), q.a.w(), r.a.w());\n",
      "7 4 32\n");
}

TEST(ClassItemTypeRefArgumentSim, SpecializesANestedClassProperty) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  class P;\n"
      "    class N;\n"
      "      X #(type(n)) a = new;\n"
      "    endclass\n"
      "    N nn = new;\n"
      "  endclass\n"
      "  P p = new;\n"
      "  initial $display(\"%0d\", p.nn.a.w());\n",
      "7\n");
}

TEST(ClassItemTypeRefArgumentSim, TakesEachOperand) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  localparam logic [2:0] L = 1;\n"
      "  pk::K k;\n"
      "  class P;\n"
      "    X #(type(n + 10'd0)) a = new;\n"
      "    X #(.T(type(L))) b = new;\n"
      "    X #(type(pk::w9)) c = new;\n"
      "    X #(.T(type(pk::t))) d = new;\n"
      "    X #(type(k)) e = new;\n"
      "    X #(.T(type(logic [5:0]))) g = new;\n"
      "    X #(.T(type(n + 10'd0))) h = new;\n"
      "    X #(type(L)) i = new;\n"
      "    X #(.T(type(pk::w9))) j = new;\n"
      "    X #(type(pk::t)) l = new;\n"
      "    X #(.T(type(k))) m = new;\n"
      "  endclass\n"
      "  P p = new;\n"
      "  pk::K o = new;\n"
      "  initial begin\n"
      "    p.e.v = o;\n"
      "    p.m.v = o;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", p.a.w(), p.b.w(), p.c.w(),\n"
      "             p.d.w(), p.e.v.m, p.g.w());\n"
      "    $display(\"%0d %0d %0d %0d %0d\", p.h.w(), p.i.w(), p.j.w(),\n"
      "             p.l.w(), p.m.v.m);\n"
      "  end\n",
      "10 3 9 12 5 6\n10 3 9 12 5\n");
}

constexpr std::string_view kClassItems[] = {
    "X #(type(@)) a;",
    "static X #(type(@)) a;",
    "typedef X #(type(@)) a;",
    "function void f(); X #(type(@)) a; endfunction",
    "function void f(X #(type(@)) a); endfunction",
    "class N; X #(type(@)) a; endclass",
};

std::string WithOperand(std::string_view item, std::string_view operand) {
  std::string text(item);
  return text.replace(text.find('@'), 1, operand);
}

void ExpectOperandsJudged(const Place& place, std::string_view item) {
  for (std::string_view operand : {"pk::w9", "nosuch", "top.u.hv"}) {
    const std::string kSource = std::string(place.open)
                                    .append("class P; ")
                                    .append(WithOperand(item, operand))
                                    .append(" endclass\n")
                                    .append(place.close);
    SCOPED_TRACE(kSource);
    SimFixture f;
    ElaborateSrc(std::string(kClasses).append(kSource), f);
    const auto kErrorLine = static_cast<uint32_t>(
        kFirstLine + std::ranges::count(place.open, '\n'));
    EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                            "parameter value assignment for type parameter "
                            "'T' of 'X' does not name a type",
                            kErrorLine, "6.20.3"),
              operand == "nosuch");
    EXPECT_EQ(
        ReportedError(f.diag.Diagnostics(),
                      "type operator argument uses a hierarchical reference, "
                      "which the type operator does not accept",
                      kErrorLine, "6.23"),
        operand == "top.u.hv");
    EXPECT_EQ(f.has_errors, operand != "pk::w9");
  }
}

TEST(ClassItemTypeRefArgumentElab, OperandNamesATypeWithoutAHierarchicalName) {
  for (const Place& place : kPlaces) {
    for (std::string_view item : kClassItems) ExpectOperandsJudged(place, item);
  }
}

}  // namespace
