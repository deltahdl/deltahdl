#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kScope =
    "class X #(type T = int);\n"
    "  static int s = 1;\n"
    "  static function int w(); T v; return $bits(v); endfunction\n"
    "endclass\n"
    "class Z #(int W = 1, type T = int);\n"
    "  static function int w(); T v; return $bits(v) * 10 + W; endfunction\n"
    "endclass\n"
    "logic [6:0] n;\n"
    "localparam logic [2:0] L = 1;\n"
    "pk::K k;\n";

struct ConstraintPlace {
  std::string_view open;
  std::string_view use;
  std::string_view close;
};

constexpr ConstraintPlace kPlaces[] = {
    {"module top;\n", "", "endmodule\n"},
    {"interface itf;\n", "", "endinterface\nmodule top; itf i(); endmodule\n"},
    {"program p;\n", "", "endprogram\nmodule top; p i(); endmodule\n"},
    {"package q;\n", "endpackage\nmodule top;\nimport q::*;\n", "endmodule\n"},
    {"", "module top;\n", "endmodule\n"},
};

std::string InPlace(const ConstraintPlace& place, std::string_view cls,
                    std::string_view use) {
  return std::string(
             "package pk;\n"
             "  typedef logic [11:0] t;\n"
             "  logic [8:0] w9;\n"
             "  class K; int m = 5; endclass\n"
             "endpackage\n"
             "module m; int hv; endmodule\n")
      .append(place.open)
      .append(kScope)
      .append(cls)
      .append(place.use)
      .append(use)
      .append(place.close);
}

void ExpectPrinted(std::string_view cls, std::string_view use,
                   std::string_view printed) {
  for (const ConstraintPlace& place : kPlaces) {
    const std::string kSource = InPlace(place, cls, use);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f), printed);
  }
}

TEST(ScopePrefixTypeRefConstraintSim, StandsInEachFormOfAConstraint) {
  ExpectPrinted(
      "class C;\n"
      "  rand int a, b, d, e, f, g, h, p, q[2];\n"
      "  logic [2:0] i;\n"
      "  constraint k1 { a == X#(type(n))::w(); }\n"
      "  constraint k2 { X#(type(n))::w() == 7 -> b == X#(type(n))::w(); }\n"
      "  constraint k3 { if (X#(type(n))::w() == 7) d == 1; else d == 2; }\n"
      "  constraint k4 {\n"
      "    foreach (q[i]) q[i] == X#(type(n))::w() + X#(type(i))::w();\n"
      "  }\n"
      "  constraint k5 { e inside {X#(type(n))::w()}; }\n"
      "  constraint k6 { f dist {X#(type(n))::w() := 1}; }\n"
      "  constraint k7 { soft g == X#(type(n))::w(); }\n"
      "  constraint k8 {\n"
      "    h dist {[X#(type(n))::w() : X#(type(n))::w()] :/ 1};\n"
      "  }\n"
      "  constraint k9 { soft p dist {X#(type(n))::w() := 1}; }\n"
      "endclass\n",
      "C c = new;\n"
      "initial begin\n"
      "  if (c.randomize() == 0) $display(\"fails\");\n"
      "  $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d %0d\", c.a, c.b,\n"
      "           c.d, c.q[0], c.q[1], c.e, c.f, c.g, c.h, c.p);\n"
      "end\n",
      "7 7 1 39 39 7 7 7 7 7\n");
}

TEST(ScopePrefixTypeRefConstraintSim, StandsInAnExternBlock) {
  ExpectPrinted(
      "class C;\n"
      "  rand int a;\n"
      "  extern constraint k1;\n"
      "endclass\n"
      "constraint C::k1 { a == X#(type(n))::w(); }\n",
      "C c = new;\n"
      "initial begin\n"
      "  if (c.randomize() == 0) $display(\"fails\");\n"
      "  $display(\"%0d\", c.a);\n"
      "end\n",
      "7\n");
}

TEST(ScopePrefixTypeRefConstraintSim, ClassesPropertyHidesTheScopesName) {
  ExpectPrinted(
      "class B; logic [4:0] v; endclass\n"
      "class C extends B;\n"
      "  rand int a, b, d;\n"
      "  logic [1:0] n;\n"
      "  constraint k1 { a == X#(type(n))::w(); b == X#(type(v))::w(); }\n"
      "  constraint k2 { d == X#(type(this.n))::w(); }\n"
      "endclass\n"
      "class G #(type U = int);\n"
      "  U u;\n"
      "  rand int a;\n"
      "  constraint k1 { a == X#(type(u))::w(); }\n"
      "endclass\n",
      "C c = new;\n"
      "G#(byte) g8 = new;\n"
      "G#(logic [2:0]) g3 = new;\n"
      "initial begin\n"
      "  if (c.randomize() == 0 || g8.randomize() == 0 ||\n"
      "      g3.randomize() == 0)\n"
      "    $display(\"fails\");\n"
      "  $display(\"%0d %0d %0d %0d %0d\", c.a, c.b, c.d, g8.a, g3.a);\n"
      "end\n",
      "2 5 2 8 3\n");
}

TEST(ScopePrefixTypeRefConstraintSim, TakesEachOperand) {
  ExpectPrinted(
      "class C;\n"
      "  rand int a, b, d, e, f, g, h, i;\n"
      "  constraint k1 { a == X#(type(n + 10'd0))::w(); }\n"
      "  constraint k2 { b == X#(.T(type(L)))::w(); }\n"
      "  constraint k3 { d == X#(type(pk::w9))::w(); }\n"
      "  constraint k4 { e == X#(.T(type(pk::t)))::w(); }\n"
      "  constraint k5 { f == X#(type(logic [5:0]))::w(); }\n"
      "  constraint k6 { g == X#(type(k))::s; }\n"
      "  constraint k7 { h == Z#(3, type(n))::w(); }\n"
      "  constraint k8 { i == Z#(.W(4), .T(type(L)))::w(); }\n"
      "endclass\n",
      "C c = new;\n"
      "initial begin\n"
      "  X#(pk::K)::s = 2;\n"
      "  if (c.randomize() == 0) $display(\"fails\");\n"
      "  $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", c.a, c.b, c.d, c.e,\n"
      "           c.f, c.g, c.h, c.i);\n"
      "end\n",
      "10 3 9 12 6 2 73 34\n");
}

void ExpectOneReport(const std::string& source, std::string_view operand,
                     uint32_t line) {
  SCOPED_TRACE(source);
  SimFixture f;
  ElaborateSrc(source, f);
  EXPECT_EQ(f.diag.Diagnostics().size(), operand == "pk::w9" ? 0U : 1U);
  if (operand == "nosuch") {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "parameter value assignment for type parameter "
                              "'T' of 'X' does not name a type",
                              line, "6.20.3"));
  } else if (operand == "u.hv") {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "type operator argument uses a hierarchical reference, "
                      "which the type operator does not accept",
                      line, "6.23"));
  }
}

TEST(ScopePrefixTypeRefConstraintElab,
     OperandNamesATypeWithoutAHierarchicalName) {
  for (std::string_view block :
       {"{ a == X#(type(@))::w(); }", "{ a == 1 -> b == X#(type(@))::w(); }",
        "{ foreach (q[i]) q[i] == X#(type(@))::w(); }",
        "{ a dist {X#(type(@))::w() := 1}; }",
        "{ soft a == X#(type(@))::w(); }"}) {
    for (std::string_view operand : {"pk::w9", "nosuch", "u.hv"}) {
      std::string text(block);
      text.replace(text.find('@'), 1, operand);
      const std::string kSource =
          InPlace(kPlaces[0],
                  std::string("class C;\nrand int a, b, q[2];\nconstraint k1 ")
                      .append(text)
                      .append("\nendclass\n"),
                  "m u();\n");
      const auto kLine = static_cast<uint32_t>(
          std::ranges::count(
              std::string_view(kSource).substr(0, kSource.find(text)), '\n') +
          1);
      ExpectOneReport(kSource, operand, kLine);
    }
  }
}

}  // namespace
