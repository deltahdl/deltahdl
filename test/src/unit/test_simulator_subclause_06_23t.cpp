#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_type_ref_operand.h"

using namespace delta;

namespace {

constexpr std::string_view kPackage =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  logic [8:0] w9;\n"
    "  class K; int m = 5; endclass\n"
    "endpackage\n"
    "module m; int hv; endmodule\n";

constexpr std::string_view kDeclared =
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

struct Place {
  std::string_view open;
  std::string_view between;
  std::string_view close;
};

constexpr Place kPlaces[] = {
    {"module top;\nint v = 7, u = 1;\n", "", "endmodule\n"},
    {"interface itf;\nint v = 7, u = 1;\n", "",
     "endinterface\nmodule top; itf i(); endmodule\n"},
    {"program p;\nint v = 7, u = 1;\n", "",
     "endprogram\nmodule top; p i(); endmodule\n"},
    {"module top;\nint v = 7, u = 1;\nif (1) begin : gb\n", "",
     "end\nendmodule\n"},
    {"package q;\nint v = 7, u = 1;\n",
     "endpackage\nmodule top;\nimport q::*;\n", "endmodule\n"},
    {"int v = 7, u = 1;\n", "module top;\n", "endmodule\n"},
};

std::string InPlace(const Place& place, std::string_view declared,
                    std::string_view use) {
  return std::string(kPackage)
      .append(place.open)
      .append(kDeclared)
      .append(declared)
      .append(place.between)
      .append(use)
      .append(place.close);
}

void ExpectEachPlacePrints(std::string_view declared, std::string_view use,
                           std::string_view printed) {
  for (const Place& place : kPlaces) {
    const std::string kSource = InPlace(place, declared, use);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f), printed);
  }
}

TEST(ScopePrefixTypeRefCovergroupSim, StandsInACoverpointAndItsBins) {
  ExpectEachPlacePrints(
      "covergroup c1;\n"
      "  coverpoint X#(type(n))::w() iff (X#(type(n))::w() == 7) {\n"
      "    bins b = {7};\n"
      "  }\n"
      "endgroup\n"
      "covergroup c2;\n"
      "  coverpoint v {\n"
      "    bins b = {[X#(type(n))::w() : X#(type(n))::w()]}\n"
      "      iff (X#(type(n))::w() == 7);\n"
      "  }\n"
      "endgroup\n"
      "covergroup c3;\n"
      "  coverpoint v { bins b = (5 => X#(type(n))::w()); }\n"
      "endgroup\n"
      "covergroup c4;\n"
      "  coverpoint v { bins b[] = {[0:15]} with (item == X#(type(n))::w()); "
      "}\n"
      "endgroup\n",
      "c1 g1 = new;\n"
      "c2 g2 = new;\n"
      "c3 g3 = new;\n"
      "c4 g4 = new;\n"
      "initial begin\n"
      "  v = 5;\n"
      "  g1.sample(); g2.sample(); g3.sample(); g4.sample();\n"
      "  v = 7;\n"
      "  g1.sample(); g2.sample(); g3.sample(); g4.sample();\n"
      "  $display(\"%0.0f %0.0f %0.0f %0.0f\", g1.get_inst_coverage(),\n"
      "           g2.get_inst_coverage(), g3.get_inst_coverage(),\n"
      "           g4.get_inst_coverage());\n"
      "end\n",
      "100 100 100 100\n");
}

TEST(ScopePrefixTypeRefCovergroupSim, StandsInACross) {
  ExpectEachPlacePrints(
      "covergroup c1;\n"
      "  a: coverpoint v { bins b[] = {[6:7]}; }\n"
      "  c: coverpoint u { bins o = {1}; }\n"
      "  x: cross a, c iff (X#(type(n))::w() == 7) {\n"
      "    ignore_bins s = binsof(a) intersect {X#(type(n))::w() - 1};\n"
      "  }\n"
      "endgroup\n"
      "covergroup c2;\n"
      "  a: coverpoint v { bins b[] = {[6:7]}; }\n"
      "  c: coverpoint u { bins o = {1}; }\n"
      "  x: cross a, c {\n"
      "    bins t = binsof(a) with (a == X#(type(n))::w());\n"
      "    ignore_bins r = binsof(a) intersect {6};\n"
      "  }\n"
      "endgroup\n",
      "c1 g1 = new;\n"
      "c2 g2 = new;\n"
      "initial begin\n"
      "  g1.sample(); g2.sample();\n"
      "  $display(\"%0.0f %0.0f\", g1.x.get_inst_coverage(),\n"
      "           g2.x.get_inst_coverage());\n"
      "end\n",
      "100 100\n");
}

TEST(ScopePrefixTypeRefCovergroupSim, StandsInAnEventAnOptionAndADefault) {
  ExpectEachPlacePrints(
      "logic c = 0;\n"
      "covergroup c1 @(posedge c iff X#(type(n))::w() == 7);\n"
      "  coverpoint v { bins b = {7}; }\n"
      "endgroup\n"
      "covergroup c2;\n"
      "  option.at_least = X#(type(n))::w() - 6;\n"
      "  coverpoint v { bins b = {7}; }\n"
      "endgroup\n"
      "covergroup c3 (int d = X#(type(n))::w());\n"
      "  coverpoint v { bins b = {d}; }\n"
      "endgroup\n",
      "c1 g1 = new;\n"
      "c2 g2 = new;\n"
      "c3 g3 = new;\n"
      "initial begin\n"
      "  #1 c = 1;\n"
      "  g2.sample(); g3.sample();\n"
      "  #1 $display(\"%0.0f %0.0f %0d %0.0f\", g1.get_inst_coverage(),\n"
      "              g2.get_inst_coverage(), g2.option.at_least,\n"
      "              g3.get_inst_coverage());\n"
      "end\n",
      "100 100 1 100\n");
}

TEST(ScopePrefixTypeRefCovergroupSim, FormalHidesTheScopesName) {
  ExpectEachPlacePrints(
      "covergroup c1 (logic [2:0] n);\n"
      "  coverpoint v { bins b = {X#(type(n))::w() + 4}; }\n"
      "endgroup\n"
      "covergroup c2 with function sample (logic [2:0] n, int s);\n"
      "  coverpoint X#(type(n))::w() + s { bins b = {7}; }\n"
      "endgroup\n",
      "c1 g1 = new(0);\n"
      "c2 g2 = new;\n"
      "initial begin\n"
      "  g1.sample(); g2.sample(0, 4);\n"
      "  $display(\"%0.0f %0.0f\", g1.get_inst_coverage(),\n"
      "           g2.get_inst_coverage());\n"
      "end\n",
      "100 100\n");
}

TEST(ScopePrefixTypeRefCovergroupSim, ClassesPropertyHidesTheScopesName) {
  ExpectEachPlacePrints(
      "class C;\n"
      "  logic [4:0] n;\n"
      "  int v = 7;\n"
      "  covergroup cg;\n"
      "    coverpoint X#(type(n))::w() + 2 { bins b = {7}; }\n"
      "    coverpoint v { bins b = {X#(type(n))::w() + 2}; }\n"
      "  endgroup\n"
      "  function new(); cg = new; endfunction\n"
      "endclass\n",
      "C o = new;\n"
      "initial begin\n"
      "  o.cg.sample();\n"
      "  $display(\"%0.0f\", o.cg.get_inst_coverage());\n"
      "end\n",
      "100\n");
}

TEST(ScopePrefixTypeRefCovergroupSim, StandsInAChecker) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kPackage).append(kDeclared).append(
                           "checker ck(logic c);\n"
                           "  logic [4:0] n;\n"
                           "  covergroup cg @(posedge c);\n"
                           "    coverpoint X#(type(n))::w() {\n"
                           "      bins b = {X#(type(L))::w() + 2};\n"
                           "    }\n"
                           "  endgroup\n"
                           "  cg g = new;\n"
                           "endchecker\n"
                           "module top;\n"
                           "  logic c = 0;\n"
                           "  ck k(c);\n"
                           "  initial begin\n"
                           "    #1 c = 1;\n"
                           "    #1 $display(\"%0.0f\", "
                           "k.g.get_inst_coverage());\n"
                           "  end\n"
                           "endmodule\n"),
                       f),
            "100\n");
}

TEST(ScopePrefixTypeRefCovergroupSim, TakesEachOperand) {
  ExpectEachPlacePrints(
      "covergroup cg;\n"
      "  coverpoint X#(type(n + 10'd0))::w() { bins b = {10}; }\n"
      "  coverpoint X#(.T(type(L)))::w() { bins b = {3}; }\n"
      "  coverpoint X#(type(pk::w9))::w() { bins b = {9}; }\n"
      "  coverpoint X#(.T(type(pk::t)))::w() { bins b = {12}; }\n"
      "  coverpoint X#(type(logic [5:0]))::w() { bins b = {6}; }\n"
      "  coverpoint X#(type(k))::s { bins b = {2}; }\n"
      "  coverpoint Z#(3, type(n))::w() { bins b = {73}; }\n"
      "  coverpoint Z#(.W(4), .T(type(L)))::w() { bins b = {34}; }\n"
      "endgroup\n",
      "cg g = new;\n"
      "initial begin\n"
      "  X#(pk::K)::s = 2;\n"
      "  g.sample();\n"
      "  $display(\"%0.0f\", g.get_inst_coverage());\n"
      "end\n",
      "100\n");
}

TEST(ScopePrefixTypeRefCovergroupElab,
     OperandNamesATypeWithoutAHierarchicalName) {
  for (std::string_view group :
       {"covergroup cg; coverpoint X#(type(@))::w(); endgroup",
        "covergroup cg; coverpoint v { bins b = {X#(type(@))::w()}; } "
        "endgroup",
        "class C; covergroup cg; coverpoint X#(type(@))::w(); endgroup "
        "endclass"}) {
    for (std::string_view operand : {"pk::w9", "nosuch", "mu.hv"}) {
      std::string text(group);
      text.replace(text.find('@'), 1, operand);
      const std::string kBefore =
          InPlace(kPlaces[0], "m mu();\n", "").substr(0, std::string::npos);
      const std::string kHead = std::string(kBefore).substr(
          0, kBefore.size() - kPlaces[0].close.size());
      ExpectTypeRefOperandReport(
          std::string(kHead).append(text).append("\nendmodule\n"), operand,
          static_cast<uint32_t>(std::ranges::count(kHead, '\n') + 1));
    }
  }
}

}  // namespace
