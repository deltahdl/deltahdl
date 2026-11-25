#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kShared =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  logic [8:0] w9;\n"
    "  parameter logic [4:0] P5 = 3;\n"
    "  class K; int m = 5; endclass\n"
    "  typedef struct packed {logic [4:0] a;} st;\n"
    "  parameter type PT = logic [3:0];\n"
    "endpackage\n";

constexpr std::string_view kClasses =
    "class X #(type T = int);\n"
    "  T v;\n"
    "  function int w(); return $bits(v); endfunction\n"
    "endclass\n"
    "class Z #(int W = 1, type T = int);\n"
    "  T v;\n"
    "  function int w(); return $bits(v) * 10 + W; endfunction\n"
    "endclass\n";

constexpr std::string_view kOperands =
    "  logic [6:0] n;\n"
    "  localparam logic [2:0] L = 1;\n"
    "  pk::K k;\n";

constexpr uint32_t kFirstLine = 17;

struct Scope {
  std::string_view open;
  std::string_view close;
  std::string_view name;
};

constexpr Scope kScopes[] = {
    {"package q;\n", "endpackage\n", "q::"},
    {"", "", ""},
};

std::string Use(const Scope& scope, std::string_view body) {
  std::string text(body);
  for (std::size_t at = text.find('@'); at != std::string::npos;
       at = text.find('@')) {
    text.replace(at, 1, scope.name);
  }
  return text;
}

void ExpectFromEachScope(std::string_view items, std::string_view use,
                         std::string_view printed) {
  for (const Scope& scope : kScopes) {
    const std::string kSource = std::string(scope.open)
                                    .append(kClasses)
                                    .append(kOperands)
                                    .append(items)
                                    .append(scope.close)
                                    .append("module top;\n")
                                    .append(Use(scope, use))
                                    .append("endmodule\n");
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(std::string(kShared).append(kSource), f), printed);
  }
}

TEST(UnitClassTypeRefArgumentSim, TakesEachOperandOfAProperty) {
  ExpectFromEachScope(
      "  class P;\n"
      "    X #(type(n + 10'd0)) a = new;\n"
      "    X #(type({n, n})) b = new;\n"
      "    X #(type(n[2:0])) c = new;\n"
      "    X #(type(5'd3)) d = new;\n"
      "    X #(.T(type(L))) e = new;\n"
      "    X #(type(pk::w9)) f = new;\n"
      "    X #(.T(type(pk::P5))) g = new;\n"
      "    X #(type(k)) h = new;\n"
      "    X #(type(n)) i = new;\n"
      "    X #(type(logic [5:0])) j = new;\n"
      "    X #(.T(type(pk::t))) l = new;\n"
      "    Z #(3, type(n + 10'd0)) m = new;\n"
      "    Z #(.T(type(L)), .W(4)) o = new;\n"
      "  endclass\n",
      "  @P p = new;\n"
      "  pk::K o = new;\n"
      "  initial begin\n"
      "    p.h.v = o;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", p.a.w(), p.b.w(),\n"
      "             p.c.w(), p.d.w(), p.e.w(), p.f.w(), p.g.w(), p.h.v.m);\n"
      "    $display(\"%0d %0d %0d %0d %0d\", p.i.w(), p.j.w(), p.l.w(),\n"
      "             p.m.w(), p.o.w());\n"
      "  end\n",
      "10 14 3 5 3 9 5 5\n7 6 12 103 34\n");
}

TEST(UnitClassTypeRefArgumentSim, SpecializesAStaticOrNestedClassProperty) {
  ExpectFromEachScope(
      "  class P;\n"
      "    static X #(type(n + 10'd0)) a = new;\n"
      "    class N;\n"
      "      X #(type(L)) b = new;\n"
      "      X #(type(pk::w9)) c = new;\n"
      "    endclass\n"
      "    N nn = new;\n"
      "  endclass\n",
      "  @P p = new;\n"
      "  initial $display(\"%0d %0d %0d\", p.a.w(), p.nn.b.w(), p.nn.c.w());\n",
      "10 3 9\n");
}

TEST(UnitClassTypeRefArgumentSim, SpecializesAMethodsDeclarations) {
  ExpectFromEachScope(
      "  class P;\n"
      "    function int f(X #(type(n + 10'd0)) a);\n"
      "      logic [3:0] l;\n"
      "      X #(type(l + 6'd0)) b;\n"
      "      X #(.T(type(pk::w9))) c;\n"
      "      Z #(2, type(L)) d;\n"
      "      b = new;\n"
      "      c = new;\n"
      "      d = new;\n"
      "      $display(\"%0d %0d %0d\", b.w(), c.w(), d.w());\n"
      "      return $bits(a.v);\n"
      "    endfunction\n"
      "    function X #(type(n + 10'd0)) g();\n"
      "      X #(type(n + 10'd0)) z;\n"
      "      z = new;\n"
      "      return z;\n"
      "    endfunction\n"
      "    task tk(X #(type(n + 10'd0)) a);\n"
      "      $display(\"%0d\", $bits(a.v));\n"
      "    endtask\n"
      "  endclass\n",
      "  @P p = new;\n"
      "  @X #(logic [9:0]) x;\n"
      "  initial begin\n"
      "    x = p.g();\n"
      "    $display(\"%0d %0d\", x.w(), p.f(x));\n"
      "    p.tk(x);\n"
      "  end\n",
      "6 9 32\n10 10\n10\n");
}

TEST(UnitClassPackageTypeRefSim, DeclaresAPropertyAFormalAndALocal) {
  ExpectFromEachScope(
      "  class P;\n"
      "    var type(pk::t) b;\n"
      "    static var type(pk::t) s;\n"
      "    var type(pk::K) h = new;\n"
      "    function int f(var type(pk::t) x);\n"
      "      var type(pk::t) y;\n"
      "      return $bits(x) * 100 + $bits(y);\n"
      "    endfunction\n"
      "  endclass\n"
      "  function int g(var type(pk::t) x);\n"
      "    var type(pk::t) y;\n"
      "    return $bits(x) * 100 + $bits(y);\n"
      "  endfunction\n",
      "  @P p = new;\n"
      "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(p.b), $bits(p.s),\n"
      "                   p.h.m, p.f(0), @g(0));\n",
      "12 12 5 1212 1212\n");
}

TEST(UnitClassTypeRefArgumentSim, SpecializesATypedef) {
  ExpectFromEachScope(
      "  class P;\n"
      "    typedef X #(type(n + 10'd0)) at;\n"
      "    typedef X #(.T(type(L))) bt;\n"
      "    typedef X #(type(pk::w9)) ct;\n"
      "    function int f();\n"
      "      at a;\n"
      "      bt b;\n"
      "      ct c;\n"
      "      a = new;\n"
      "      b = new;\n"
      "      c = new;\n"
      "      return a.w() * 100 + b.w() * 10 + c.w();\n"
      "    endfunction\n"
      "  endclass\n",
      "  @P p = new;\n"
      "  initial $display(\"%0d\", p.f());\n",
      "1039\n");
}

TEST(UnitClassPackageTypeRefSim, NamesAStructureOrATypeParameter) {
  ExpectFromEachScope(
      "  class P;\n"
      "    var type(pk::st) s;\n"
      "    var type(pk::PT) z;\n"
      "    X #(type(pk::PT)) x = new;\n"
      "  endclass\n",
      "  @P p = new;\n"
      "  initial begin\n"
      "    p.s.a = 9;\n"
      "    $display(\"%0d %0d %0d %0d\", $bits(p.s), p.s.a, $bits(p.z),\n"
      "             p.x.w());\n"
      "  end\n",
      "5 9 4 4\n");
}

TEST(UnitClassPackageTypeRefSim, NamesAMemberAValueOrAUnitsVariable) {
  ExpectFromEachScope(
      "  pk::st r;\n"
      "  class P;\n"
      "    var type(r.a) a;\n"
      "    var type(pk::w9) b;\n"
      "  endclass\n",
      "  @P p = new;\n"
      "  initial $display(\"%0d %0d\", $bits(p.a), $bits(p.b));\n",
      "5 9\n");
  SimFixture f;
  EXPECT_EQ(RunCapture("logic [6:0] n;\n"
                       "class P; var type($unit::n) a; endclass\n"
                       "module top;\n"
                       "  P p = new;\n"
                       "  initial $display(\"%0d\", $bits(p.a));\n"
                       "endmodule\n",
                       f),
            "7\n");
}

TEST(UnitClassPackageTypeRefElab, ClassScopedTypeIsAccepted) {
  for (const Scope& scope : kScopes) {
    for (std::string_view operand : {"C::u", "W#(byte)::u", "pk::t"}) {
      const std::string kSource =
          std::string(kShared)
              .append(scope.open)
              .append(
                  "class C; typedef logic [6:0] u; endclass\n"
                  "class W #(type T = int); typedef T u; endclass\n"
                  "class P; var type(")
              .append(operand)
              .append(") a; endclass\n")
              .append(scope.close)
              .append("module top; endmodule\n");
      SCOPED_TRACE(kSource);
      SimFixture f;
      ElaborateSrc(kSource, f);
      EXPECT_FALSE(f.has_errors);
      EXPECT_TRUE(f.diag.Diagnostics().empty());
    }
  }
}

constexpr std::string_view kClassItems[] = {
    "X #(type(@)) a;",
    "static X #(type(@)) a;",
    "typedef X #(type(@)) a;",
    "function void f(); X #(type(@)) a; endfunction",
    "function void f(X #(type(@)) a); endfunction",
    "class N; X #(type(@)) a; endclass",
};

void ExpectOperandsJudged(const Scope& scope, std::string_view item) {
  for (std::string_view operand : {"pk::w9", "nosuch", "top.u.hv"}) {
    std::string text(item);
    text.replace(text.find('@'), 1, operand);
    const std::string kSource = std::string(scope.open)
                                    .append(kClasses)
                                    .append("class P; ")
                                    .append(text)
                                    .append(" endclass\n")
                                    .append(scope.close)
                                    .append(
                                        "module z; logic [3:0] hv; endmodule\n"
                                        "module top; z u(); endmodule\n");
    SCOPED_TRACE(kSource);
    SimFixture f;
    ElaborateSrc(std::string(kShared).append(kSource), f);
    const uint32_t kErrorLine = kFirstLine + (scope.open.empty() ? 0 : 1);
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
    EXPECT_EQ(f.diag.Diagnostics().size(), operand == "pk::w9" ? 0U : 1U);
    EXPECT_EQ(f.has_errors, operand != "pk::w9");
  }
}

TEST(UnitClassTypeRefArgumentElab, OperandNamesATypeWithoutAHierarchicalName) {
  for (const Scope& scope : kScopes) {
    for (std::string_view item : kClassItems) ExpectOperandsJudged(scope, item);
  }
}

}  // namespace
