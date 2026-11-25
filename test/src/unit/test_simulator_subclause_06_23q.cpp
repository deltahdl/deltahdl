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
    "  class K; int m = 5; endclass\n"
    "endpackage\n"
    "class X #(type T = int);\n"
    "  static int s = 1;\n"
    "  static function int w(); T v; return $bits(v); endfunction\n"
    "  static function int m(); T v = '1; return v; endfunction\n"
    "endclass\n"
    "module m; int hv; endmodule\n";

constexpr std::string_view kNames =
    "logic c = 0;\n"
    "logic [6:0] n;\n"
    "localparam logic [2:0] L = 1;\n"
    "pk::K k;\n"
    "int held = 0;\n"
    "task hold(int at); held[at] = 1; endtask\n"
    "initial begin\n"
    "  X#(pk::K)::s = 2;\n"
    "  #1 c = 1;\n"
    "  #1 $display(\"%b\", held);\n"
    "end\n";

struct AssertionPlace {
  std::string_view open;
  std::string_view close;
};

constexpr AssertionPlace kPlaces[] = {
    {"module top;\n", "endmodule\n"},
    {"module top;\nlogic [1:0] n;\nif (1) begin : b\n", "end\nendmodule\n"},
    {"interface itf;\n", "endinterface\nmodule top; itf i(); endmodule\n"},
    {"program p;\n", "endprogram\nmodule top; p i(); endmodule\n"},
};

std::string InPlace(const AssertionPlace& place, std::string_view items) {
  return std::string(kClasses)
      .append(place.open)
      .append(kNames)
      .append(items)
      .append(place.close);
}

void ExpectHeld(std::string_view items, std::string_view held) {
  for (const AssertionPlace& place : kPlaces) {
    const std::string kSource = InPlace(place, items);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f),
              std::string(32 - held.size(), '0').append(held).append("\n"));
  }
}

TEST(ScopePrefixTypeRefAssertionSim, StandsInADeclaredPropertyAndSequence) {
  ExpectHeld(
      "property p; @(posedge c) X#(type(n))::w() == 7; endproperty\n"
      "property t; @(posedge c) 1 ##0 X#(type(n))::w() == 7; endproperty\n"
      "sequence q; X#(type(n))::w() == 7; endsequence\n"
      "sequence e; @(posedge c) 1 ##0 X#(type(n))::w() == 7; endsequence\n"
      "property d; @(posedge c) disable iff (X#(type(n))::w() == 7) 0;\n"
      "endproperty\n"
      "property i; @(posedge c iff X#(type(n))::w() == 7) 1; endproperty\n"
      "assert property (p) held[0] = 1;\n"
      "assert property (t) held[1] = 1;\n"
      "assert property (@(posedge c) q) held[2] = 1;\n"
      "assert property (e) held[3] = 1;\n"
      "assert property (d) else held[4] = 1;\n"
      "assert property (i) held[5] = 1;\n",
      "101111");
}

TEST(ScopePrefixTypeRefAssertionSim, StandsInAnAssertionsProperty) {
  ExpectHeld(
      "assert property (@(posedge c) 1 ##0 X#(type(n))::w() == 7)\n"
      "  held[0] = 1;\n"
      "assert property (@(posedge c) X#(type(n))::w() == 7 |->\n"
      "                 X#(type(L))::w() == 3) held[1] = 1;\n"
      "assert property (@(posedge c) X#(type(n))::w() == 32 |-> 0)\n"
      "  held[2] = 1;\n"
      "assert property (@(posedge c) disable iff (X#(type(n))::w() == 32) 1)\n"
      "  held[3] = 1;\n"
      "assert property (@(posedge c iff X#(type(n))::w() == 7) 1)\n"
      "  held[4] = 1;\n"
      "assert property (@(posedge c) if (X#(type(n))::w() == 7) 1 else 0)\n"
      "  held[5] = 1;\n"
      "assert property (@(posedge c) case (X#(type(n))::w())\n"
      "                 7: 1; default: 0; endcase) held[6] = 1;\n"
      "assert property (@(posedge c) case (7)\n"
      "                 X#(type(n))::w(): 1; default: 0; endcase)\n"
      "  held[7] = 1;\n"
      "assert property (@(posedge c) not (X#(type(n))::w() == 32))\n"
      "  held[8] = 1;\n",
      "111111111");
}

TEST(ScopePrefixTypeRefAssertionSim, StandsInEachKindOfAssertion) {
  ExpectHeld(
      "assume property (@(posedge c) 1 ##0 X#(type(n))::w() == 7)\n"
      "  held[0] = 1;\n"
      "cover property (@(posedge c) 1 ##0 X#(type(n))::w() == 7)\n"
      "  held[1] = 1;\n"
      "cover sequence (@(posedge c) 1 ##0 X#(type(n))::w() == 7)\n"
      "  held[2] = 1;\n"
      "restrict property (@(posedge c) 1 ##0 X#(type(n))::w() == 7);\n"
      "initial #1 assert #0 (X#(type(n))::w() == 7) hold(3);\n"
      "initial begin\n"
      "  assert property (@(posedge c) 1 ##0 X#(type(n))::w() == 7)\n"
      "    held[4] = 1;\n"
      "end\n"
      "initial begin\n"
      "  #1 assert #0 (X#(type(n))::w() == 7) hold(5);\n"
      "  assert final (X#(type(n))::w() == 7) hold(6);\n"
      "  assert (X#(type(n))::w() == 7) held[7] = 1;\n"
      "end\n",
      "11111111");
}

TEST(ScopePrefixTypeRefAssertionSim, FormalOrLocalVariableHidesTheScopesName) {
  ExpectHeld(
      "property p(logic [2:0] n);\n"
      "  @(posedge c) 1 ##0 X#(type(n))::w() == 3;\n"
      "endproperty\n"
      "sequence q(byte n); 1 ##0 X#(type(n))::w() == 8; endsequence\n"
      "property v;\n"
      "  int x = X#(type(n))::w();\n"
      "  @(posedge c) 1 ##0 x == 7;\n"
      "endproperty\n"
      "property a;\n"
      "  int x;\n"
      "  @(posedge c) (1, x = X#(type(n))::w()) ##0 x == 7;\n"
      "endproperty\n"
      "property l;\n"
      "  logic [1:0][4:0] n = 0;\n"
      "  @(posedge c) 1 ##0 (n == 0 && X#(type(n))::w() == 10);\n"
      "endproperty\n"
      "property y;\n"
      "  shortint n = 0;\n"
      "  @(posedge c) 1 ##0 (n == 0 && X#(type(n))::w() == 16);\n"
      "endproperty\n"
      "property z;\n"
      "  pk::t n = 0;\n"
      "  @(posedge c) 1 ##0 (n == 0 && X#(type(n))::w() == 12);\n"
      "endproperty\n"
      "property s;\n"
      "  logic signed [2:0] n = 0; shortint h = 0; int unsigned u = 0;\n"
      "  @(posedge c) 1 ##0 (n == 0 && h == 0 && u == 0 &&\n"
      "    X#(type(n))::m() == -1 && X#(type(h))::m() == -1 &&\n"
      "    X#(type(u))::m() == -1 && X#(type(u))::w() == 32);\n"
      "endproperty\n"
      "property g; logic [2:0] n = 0; bit signed [2:0] b = 0;\n"
      "  @(posedge c) 1 ##0 (n == 0 && b == 0 &&\n"
      "    X#(type(n))::m() == 7 && X#(type(b))::m() == -1);\n"
      "endproperty\n"
      "sequence d(int x = X#(type(n))::w()); 1 ##0 x == 7; endsequence\n"
      "property o(logic [2:0] m);\n"
      "  @(posedge c) 1 ##0 X#(type(m))::w() == 3;\n"
      "endproperty\n"
      "assert property (p(1)) held[0] = 1;\n"
      "assert property (@(posedge c) q(1)) held[1] = 1;\n"
      "assert property (v) held[2] = 1;\n"
      "assert property (a) held[3] = 1;\n"
      "assert property (l) held[4] = 1;\n"
      "assert property (y) held[5] = 1;\n"
      "assert property (z) held[6] = 1;\n"
      "assert property (@(posedge c) d()) held[7] = 1;\n"
      "assert property (o(1)) held[8] = 1;\n"
      "assert property (s) held[9] = 1;\n"
      "assert property (g) held[10] = 1;\n",
      "11111111111");
}

TEST(ScopePrefixTypeRefAssertionSim, StandsInAClockingBlockAndAnActual) {
  const std::string kSource =
      InPlace(kPlaces[0],
              "clocking cb @(posedge c iff X#(type(n))::w() == 7);\n"
              "  property p; 1 ##0 X#(type(n))::w() == 7; endproperty\n"
              "endclocking\n"
              "property q(property r); @(posedge c) r; endproperty\n"
              "assert property (cb.p) held[0] = 1;\n"
              "always @(cb) held[1] = 1;\n"
              "assert property (q(1 ##0 X#(type(n))::w() == 7)) held[2] = 1;\n"
              "property e(x); @(posedge c) 1 ##0 x; endproperty\n"
              "assert property (e(X#(type(n))::w() == 7)) held[3] = 1;\n");
  SimFixture f;
  EXPECT_EQ(RunCapture(kSource, f), std::string(28, '0').append("1111\n"));
}

TEST(ScopePrefixTypeRefAssertionSim, StandsInADeferredAssertionItem) {
  const std::string kSource =
      InPlace(kPlaces[0], "assert #0 (X#(type(n))::w() == 7) hold(0);\n");
  SimFixture f;
  EXPECT_EQ(RunCapture(kSource, f), std::string(31, '0').append("1\n"));
}

TEST(ScopePrefixTypeRefAssertionSim, StandsInADefaultDisableIff) {
  const std::string kSource =
      InPlace(kPlaces[0],
              "default disable iff (X#(type(n))::w() == 7);\n"
              "assert property (@(posedge c) 0) else held[0] = 1;\n"
              "assert property (@(posedge c) disable iff (0) 0)\n"
              "  else held[1] = 1;\n");
  SimFixture f;
  EXPECT_EQ(RunCapture(kSource, f), std::string(30, '0').append("10\n"));
}

TEST(ScopePrefixTypeRefAssertionSim, StandsInAChecker) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kClasses).append(
                           "checker ck(input logic k);\n"
                           "logic [6:0] n;\n"
                           "property p; 1 ##0 X#(type(n))::w() == 7;\n"
                           "endproperty\n"
                           "a: assert property (@(posedge k) p)\n"
                           "  $display(\"p\"); else $display(\"fails\");\n"
                           "b: assert property (@(negedge k)\n"
                           "                    1 ##0 X#(type(n))::w() == 7)\n"
                           "  $display(\"own\"); else $display(\"fails\");\n"
                           "endchecker\n"
                           "module top;\n"
                           "logic [1:0] n;\n"
                           "logic k = 0;\n"
                           "ck u(k);\n"
                           "initial begin #1 k = 1; #1 k = 0; end\n"
                           "endmodule\n"),
                       f),
            "p\nown\n");
}

TEST(ScopePrefixTypeRefAssertionSim, TakesEachOperand) {
  ExpectHeld(
      "class Z #(int W = 1, type T = int);\n"
      "  static function int w(); T v; return $bits(v) * 10 + W; endfunction\n"
      "endclass\n"
      "assert property (@(posedge c) 1 ##0 X#(type(n + 10'd0))::w() == 10)\n"
      "  held[0] = 1;\n"
      "assert property (@(posedge c) 1 ##0 X#(.T(type(L)))::w() == 3)\n"
      "  held[1] = 1;\n"
      "assert property (@(posedge c) 1 ##0 X#(type(pk::w9))::w() == 9)\n"
      "  held[2] = 1;\n"
      "assert property (@(posedge c) 1 ##0 X#(.T(type(pk::t)))::w() == 12)\n"
      "  held[3] = 1;\n"
      "assert property (@(posedge c) 1 ##0 X#(type(logic [5:0]))::w() == 6)\n"
      "  held[4] = 1;\n"
      "assert property (@(posedge c) 1 ##0 X#(type(k))::s == 2)\n"
      "  held[5] = 1;\n"
      "assert property (@(posedge c) 1 ##0 Z#(3, type(n))::w() == 73)\n"
      "  held[6] = 1;\n"
      "assert property (@(posedge c) 1 ##0 Z#(.W(4), .T(type(L)))::w() == 34)\n"
      "  held[7] = 1;\n"
      "assert property (@(posedge c)\n"
      "    1 ##0 X#(type({X#(type(n))::w(), n}))::w() == 39) held[8] = 1;\n",
      "111111111");
}

constexpr std::string_view kActual =
    "property p(byte b); @(posedge c) X#(type(b))::w() == 8; endproperty "
    "assert property (p(X#(type(@))::w()));";

constexpr std::string_view kItems[] = {
    "property p; @(posedge c) X#(type(@))::w() == 1; endproperty",
    "property p; @(posedge c) 1 ##0 X#(type(@))::w() == 1; endproperty",
    "sequence q; 1 ##0 X#(type(@))::w() == 1; endsequence",
    "assert property (@(posedge c) X#(type(@))::w() == 1);",
    "assert property (@(posedge c) 1 ##0 X#(type(@))::w() == 1);",
    "assert property (@(posedge c) disable iff (X#(type(@))::s) 1);",
    "assert #0 (X#(type(@))::w() == 1);",
    "initial assert (X#(type(@))::w() == 1);",
    kActual};

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

TEST(ScopePrefixTypeRefAssertionElab,
     OperandNamesATypeWithoutAHierarchicalName) {
  for (std::string_view item : kItems) {
    for (std::string_view operand : {"pk::w9", "nosuch", "u.hv"}) {
      std::string text(item);
      text.replace(text.find('@', text.find("type(@")), 1, operand);
      const std::string kSource =
          InPlace(kPlaces[0], std::string(text).append("\nm u();\n"));
      const auto kLine = static_cast<uint32_t>(
          std::ranges::count(
              std::string_view(kSource).substr(0, kSource.rfind(text)), '\n') +
          1);
      ExpectOneReport(kSource, operand, kLine);
    }
  }
}

}  // namespace
