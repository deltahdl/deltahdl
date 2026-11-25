#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_type_ref_operand.h"

using namespace delta;

namespace {

constexpr std::string_view kClass =
    "class X #(type T = int);\n"
    "  static logic [31:0] s;\n"
    "  static function logic [31:0] w(); T v; return $bits(v); endfunction\n"
    "endclass\n";

constexpr std::string_view kPackage =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  logic [8:0] w9;\n"
    "  class K; int m = 5; endclass\n"
    "endpackage\n"
    "module show #(string N = \"\") (input logic [31:0] a, b);\n"
    "  initial #20 $display(\"%s %0d %0d\", N, a, b);\n"
    "endmodule\n";

constexpr std::string_view kNames =
    "logic [6:0] n;\n"
    "localparam logic [2:0] L = 1;\n"
    "pk::K k;\n";

struct ItemPlace {
  std::string_view open;
  std::string_view close;
  bool allows_instances;
};

constexpr ItemPlace kItemPlaces[] = {
    {"module top;\n", "endmodule\n", true},
    {"module top;\nlogic [1:0] n;\nif (1) begin : b\n", "end\nendmodule\n",
     true},
    {"interface itf;\n", "endinterface\nmodule top; itf i(); endmodule\n",
     false},
    {"program p;\n", "endprogram\nmodule top; p i(); endmodule\n", false},
};

std::string InPlace(const ItemPlace& place, std::string_view items) {
  return std::string(kPackage)
      .append(kClass)
      .append(place.open)
      .append(kNames)
      .append(items)
      .append(place.close);
}

void ExpectFromItems(std::string_view items, std::string_view printed,
                     bool needs_instances = false) {
  for (const ItemPlace& place : kItemPlaces) {
    if (needs_instances && !place.allows_instances) continue;
    const std::string kSource = InPlace(place, items);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f), printed);
  }
}

TEST(ScopePrefixTypeRefItemSim, StandsInAContinuousAssignment) {
  ExpectFromItems(
      "class Y #(type T = int); static int s; endclass\n"
      "wire [31:0] a;\n"
      "wire [31:0] b = X#(type(n))::w();\n"
      "wire [31:0] c;\n"
      "assign a = X#(type(n))::w() + 1;\n"
      "assign Y#(type(L))::s = 4;\n"
      "assign c = X#(type(n))::s;\n"
      "initial begin\n"
      "  X#(logic [6:0])::s = 9;\n"
      "  #1 $display(\"%0d %0d %0d %0d %0d\", a, b, c,\n"
      "              Y#(logic [2:0])::s, Y#(int)::s);\n"
      "end\n",
      "8 7 9 4 0\n");
}

TEST(ScopePrefixTypeRefItemSim, StandsInAVariablesInitializer) {
  ExpectFromItems(
      "int a = X#(type(n))::w();\n"
      "int b [2] = '{X#(type(n))::w(), X#(type(L))::w()};\n"
      "class D;\n"
      "  int c = X#(type(n))::w();\n"
      "  static int s = X#(type(n))::w() + 1;\n"
      "  bit [3:0] q;\n"
      "  int e = X#(type(q))::w();\n"
      "endclass\n"
      "D d = new;\n"
      "initial $display(\"%0d %0d %0d %0d %0d %0d\", a, b[0], b[1], d.c,\n"
      "                 D::s, d.e);\n",
      "7 7 3 7 8 4\n");
}

TEST(ScopePrefixTypeRefItemSim, StandsInAnInstancesConnections) {
  ExpectFromItems(
      "show #(\"o\") u(X#(type(n))::w(), X#(type(L))::w());\n"
      "show #(\"n\") v(.b(X#(type(n))::w()), .a(X#(type(L))::w()));\n",
      "o 7 3\nn 3 7\n", true);
}

TEST(ScopePrefixTypeRefItemSim, StandsInAGatesTerminalsAndDelays) {
  ExpectFromItems(
      "wire a, c, e, g;\n"
      "and g1(a, X#(type(n))::w() == 7, 1'b1);\n"
      "buf #(X#(type(n))::w()) g2(c, 1'b1);\n"
      "assign #(X#(type(n))::w()) e = 1;\n"
      "wire #(X#(type(L))::w(), X#(type(L))::w()) d = 1;\n"
      "initial begin\n"
      "  #2 $display(\"%b %b %b %b\", a, c, d, e);\n"
      "  #2 $display(\"%b %b %b %b\", a, c, d, e);\n"
      "  #4 $display(\"%b %b %b %b\", a, c, d, e);\n"
      "end\n",
      "1 x x x\n1 x 1 x\n1 1 1 1\n", true);
}

TEST(ScopePrefixTypeRefItemSim, StandsInALetAndAFormalsDefault) {
  ExpectFromItems(
      "let l = X#(type(n))::w();\n"
      "let of(x = X#(type(L))::w()) = x + 1;\n"
      "let own(logic [4:0] n) = X#(type(n))::w() + n;\n"
      "function automatic int f(int a = X#(type(n))::w());\n"
      "  return a;\n"
      "endfunction\n"
      "task automatic t(output int o, input int a = X#(type(n))::w() + 1);\n"
      "  o = a;\n"
      "endtask\n"
      "class D;\n"
      "  function int m(int a = X#(type(n))::w()); return a; endfunction\n"
      "endclass\n"
      "D d = new;\n"
      "int o;\n"
      "initial begin\n"
      "  let in = X#(type(n))::w() + 2;\n"
      "  let mine(logic [3:0] n) = X#(type(n))::w() + n;\n"
      "  t(o);\n"
      "  $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", l, of(), f(), o,\n"
      "           d.m(), in, own(1), mine(1));\n"
      "end\n",
      "7 4 7 8 7 9 6 5\n");
}

TEST(ScopePrefixTypeRefItemSim, StandsInTheUnitsLetAndDefaults) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kPackage).append(kClass).append(kNames).append(
                     "let l = X#(type(n))::w();\n"
                     "function automatic int f(int a = X#(type(n))::w());\n"
                     "  return a + l;\n"
                     "endfunction\n"
                     "class D;\n"
                     "  static function int m(int a = X#(type(L))::w());\n"
                     "    return a;\n"
                     "  endfunction\n"
                     "endclass\n"
                     "module top;\n"
                     "initial $display(\"%0d %0d\", f(), D::m());\n"
                     "endmodule\n"),
                 f),
      "14 3\n");
}

TEST(ScopePrefixTypeRefItemSim, StandsInAPackagesDefaultAndProperty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kPackage)
                     .append("package q;\n")
                     .append(kClass)
                     .append(kNames)
                     .append("function automatic int f(\n"
                             "    int a = X#(type(n))::w());\n"
                             "  return a;\n"
                             "endfunction\n"
                             "class D; int p = X#(type(L))::w();\n"
                             "endclass\n"
                             "endpackage\n"
                             "module top;\n"
                             "q::D d = new;\n"
                             "initial $display(\"%0d %0d\", q::f(), d.p);\n"
                             "endmodule\n"),
                 f),
      "7 3\n");
}

TEST(ScopePrefixTypeRefItemSim, StandsInACheckersItems) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kPackage).append(kClass).append(
                     "checker ck(input logic k);\n"
                     "logic [6:0] n;\n"
                     "int a = X#(type(n))::w();\n"
                     "logic [31:0] b;\n"
                     "assign b = X#(type(n + 9'd0))::w();\n"
                     "let l = X#(type(n))::w();\n"
                     "function int f(int q = X#(type(n))::w());\n"
                     "  return q;\n"
                     "endfunction\n"
                     "assert property (@(posedge k) 0)\n"
                     "  else $display(\"%0d %0d %0d %0d\", a, b, l, f());\n"
                     "endchecker\n"
                     "module top;\n"
                     "logic k = 0;\n"
                     "ck u(k);\n"
                     "initial #1 k = 1;\n"
                     "endmodule\n"),
                 f),
      "7 9 7 7\n");
}

TEST(ScopePrefixTypeRefItemSim, TakesEachOperand) {
  ExpectFromItems(
      "class Z #(int W = 1, type T = int);\n"
      "  static function int w(); T v; return $bits(v) * 10 + W; endfunction\n"
      "endclass\n"
      "wire [31:0] a = X#(type(n + 10'd0))::w();\n"
      "wire [31:0] b = X#(.T(type(L)))::w();\n"
      "wire [31:0] c = X#(type(pk::w9))::w();\n"
      "wire [31:0] d = X#(.T(type(pk::t)))::w();\n"
      "wire [31:0] e = X#(type(logic [5:0]))::w();\n"
      "wire [31:0] g = X#(type(k))::s;\n"
      "wire [31:0] h = Z#(3, type(n))::w();\n"
      "wire [31:0] i = Z#(.W(4), .T(type(L)))::w();\n"
      "initial begin\n"
      "  X#(pk::K)::s = 2;\n"
      "  #1 $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", a, b, c, d, e, g,\n"
      "              h, i);\n"
      "end\n",
      "10 3 9 12 6 2 73 34\n");
}

TEST(ScopePrefixTypeRefItemSim, EachInstanceTakesItsOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kPackage).append(kClass).append(
                           "module m #(int W = 2) (output wire [31:0] a);\n"
                           "logic [W-1:0] n;\n"
                           "int b = X#(type(n))::w();\n"
                           "assign a = X#(type(n))::w() * 10 + b;\n"
                           "endmodule\n"
                           "module top;\n"
                           "wire [31:0] x, y;\n"
                           "m #(3) u(x);\n"
                           "m #(5) v(y);\n"
                           "initial #1 $display(\"%0d %0d\", x, y);\n"
                           "endmodule\n"),
                       f),
            "33 55\n");
}

TEST(ScopePrefixTypeRefItemElab, OperandNamesATypeWithoutAHierarchicalName) {
  for (std::string_view item :
       {"wire [31:0] a = X#(type(@))::w();", "int a = X#(type(@))::s;",
        "wire [31:0] a; assign a = X#(.T(type(@)))::w();",
        "assign X#(type(@))::s = 1;", "let l = X#(type(@))::w();",
        "function void f(int a = X#(type(@))::w()); endfunction",
        "class D; int a = X#(type(@))::w(); endclass",
        "show u(X#(type(@))::w(), 1);",
        "wire a; buf g(a, X#(type(@))::w() == 1);"}) {
    for (std::string_view operand : {"pk::w9", "nosuch", "top.u.hv"}) {
      std::string text(item);
      text.replace(text.find('@'), 1, operand);
      const std::string kSource =
          InPlace(kItemPlaces[0], std::string(text).append("\n"));
      const auto kLine = static_cast<uint32_t>(
          std::ranges::count(
              std::string_view(kSource).substr(0, kSource.rfind(text)), '\n') +
          1);
      ExpectTypeRefOperandReport(kSource, operand, kLine);
    }
  }
}

}  // namespace
