#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_type_ref_operand.h"

using namespace delta;

namespace {

constexpr std::string_view kShared =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  logic [8:0] w9;\n"
    "  class K; int m = 5; endclass\n"
    "endpackage\n"
    "module m; int hv; endmodule\n";

constexpr std::string_view kScope =
    "class X #(type T = int);\n"
    "  static int s = 1;\n"
    "  static function int w(); T v; return $bits(v); endfunction\n"
    "endclass\n"
    "class Z #(int W = 1, type T = int);\n"
    "  static function int w(); T v; return $bits(v) * 10 + W; endfunction\n"
    "endclass\n"
    "class R; rand int a, b, d, e, f, g, h, i, q[2]; endclass\n"
    "logic [6:0] n;\n"
    "localparam logic [2:0] L = 1;\n"
    "pk::K k;\n"
    "int z;\n";

constexpr std::string_view kPlaces[][3] = {
    {"module top;\n", "", "endmodule\n"},
    {"interface itf;\n", "", "endinterface\nmodule top; itf i(); endmodule\n"},
    {"program p;\n", "", "endprogram\nmodule top; p i(); endmodule\n"},
    {"package q;\n", "endpackage\nmodule top;\nimport q::*;\n", "endmodule\n"},
    {"", "module top;\n", "endmodule\n"},
};

void ExpectPrinted(std::string_view declared, std::string_view use,
                   std::string_view printed) {
  for (const auto& [open, between, close] : kPlaces) {
    const std::string kSource = std::string(kShared)
                                    .append(open)
                                    .append(kScope)
                                    .append(declared)
                                    .append(between)
                                    .append(use)
                                    .append(close);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f), printed);
  }
}

TEST(ScopePrefixTypeRefInlineSim, StandsInEachFormOfAConstraint) {
  ExpectPrinted(
      "task automatic t();\n"
      "  R r = new;\n"
      "  if (r.randomize() with {\n"
      "        a == X#(type(n))::w();\n"
      "        X#(type(n))::w() == 7 -> b == X#(type(n))::w();\n"
      "        if (X#(type(n))::w() == 7) d == 1; else d == 2;\n"
      "        foreach (q[L]) q[L] == X#(type(n))::w() + X#(type(L))::w();\n"
      "        e inside {X#(type(n))::w()};\n"
      "        f dist {X#(type(n))::w() := 1};\n"
      "        soft g == X#(type(n))::w();\n"
      "        soft h dist {[X#(type(n))::w() : X#(type(n))::w()] :/ 1};\n"
      "      } == 0)\n"
      "    $display(\"fails\");\n"
      "  $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d\", r.a, r.b, r.d,\n"
      "           r.q[0], r.q[1], r.e, r.f, r.g, r.h);\n"
      "endtask\n",
      "initial t();\n", "7 7 1 39 39 7 7 7 7\n");
}

TEST(ScopePrefixTypeRefInlineSim, StandsInAScopeRandomize) {
  ExpectPrinted(
      "task t();\n"
      "  bit [3:0] v;\n"
      "  if (std::randomize(z) with { z == X#(type(n))::w(); } == 0)\n"
      "    $display(\"fails\");\n"
      "  if (std::randomize(v) with { v == X#(type(v))::w(); } == 0)\n"
      "    $display(\"fails\");\n"
      "  if (randomize(z) with { z > 1; z < X#(type(L))::w(); } == 0)\n"
      "    $display(\"fails\");\n"
      "  $display(\"%0d %0d\", z, v);\n"
      "endtask\n",
      "initial t();\n"
      "initial begin\n"
      "  #1 if (std::randomize(z) with { z == X#(type(n))::w(); } == 0)\n"
      "    $display(\"fails\");\n"
      "  $display(\"%0d\", z);\n"
      "end\n",
      "2 4\n7\n");
}

TEST(ScopePrefixTypeRefInlineSim, StandsInEachKindOfProcedure) {
  ExpectPrinted(
      "function automatic int f(logic [1:0] n);\n"
      "  R r = new;\n"
      "  return r.randomize() with { a == X#(type(n))::w(); } ? r.a : 0;\n"
      "endfunction\n"
      "class D;\n"
      "  rand int a;\n"
      "  logic [4:0] p;\n"
      "  function int own(); \n"
      "    void'(randomize() with { a == X#(type(p))::w(); });\n"
      "    return a;\n"
      "  endfunction\n"
      "  function int self();\n"
      "    void'(this.randomize() with { a == X#(type(p))::w() + 1; });\n"
      "    return a;\n"
      "  endfunction\n"
      "  function int other();\n"
      "    logic [2:0] v;\n"
      "    R r = new;\n"
      "    void'(r.randomize() with { a == X#(type(v))::w(); });\n"
      "    return r.a;\n"
      "  endfunction\n"
      "endclass\n",
      "D d = new;\n"
      "initial begin\n"
      "  automatic logic [3:0] n = 0;\n"
      "  automatic R r = new;\n"
      "  void'(r.randomize() with { a == X#(type(n))::w(); });\n"
      "  begin\n"
      "    automatic logic [8:0] n = 0;\n"
      "    void'(r.randomize() with { b == X#(type(n))::w(); });\n"
      "  end\n"
      "  $display(\"%0d %0d %0d %0d %0d\", r.b, f(0), d.own(), d.self(),\n"
      "           d.other());\n"
      "end\n",
      "9 2 5 6 3\n");
}

TEST(ScopePrefixTypeRefInlineSim, TakesEachOperand) {
  ExpectPrinted(
      "task automatic t();\n"
      "  R r = new;\n"
      "  X#(pk::K)::s = 2;\n"
      "  if (r.randomize() with {\n"
      "        a == X#(type(n + 10'd0))::w();\n"
      "        b == X#(.T(type(L)))::w();\n"
      "        d == X#(type(pk::w9))::w();\n"
      "        e == X#(.T(type(pk::t)))::w();\n"
      "        f == X#(type(logic [5:0]))::w();\n"
      "        g == X#(type(k))::s;\n"
      "        h == Z#(3, type(n))::w();\n"
      "        i == Z#(.W(4), .T(type(L)))::w();\n"
      "      } == 0)\n"
      "    $display(\"fails\");\n"
      "  $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", r.a, r.b, r.d, r.e,\n"
      "           r.f, r.g, r.h, r.i);\n"
      "endtask\n",
      "initial t();\n", "10 3 9 12 6 2 73 34\n");
}

TEST(ScopePrefixTypeRefInlineElab, OperandNamesATypeWithoutAHierarchicalName) {
  for (std::string_view call :
       {"r.randomize() with { a == X#(type(@))::w(); }",
        "r.randomize() with { foreach (q[i]) q[i] == X#(type(@))::w(); }",
        "std::randomize(z) with { z == X#(type(@))::w(); }"}) {
    for (std::string_view operand : {"pk::w9", "nosuch", "u.hv"}) {
      std::string text(call);
      text.replace(text.find('@'), 1, operand);
      const std::string kBefore = std::string(kShared)
                                      .append("module top;\n")
                                      .append(kScope)
                                      .append("m u();\nR r = new;\n");
      ExpectTypeRefOperandReport(
          std::string(kBefore)
              .append("initial void'(")
              .append(text)
              .append(");\nendmodule\n"),
          operand,
          static_cast<uint32_t>(std::ranges::count(kBefore, '\n') + 1));
    }
  }
}

}  // namespace
