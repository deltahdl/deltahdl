#include <gtest/gtest.h>

#include <algorithm>
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
    "  class K; int m = 5; endclass\n"
    "  class X #(type T = int);\n"
    "    static int s;\n"
    "    static function int w(); T v; return $bits(v); endfunction\n"
    "  endclass\n"
    "endpackage\n";

constexpr std::string_view kDeclarations =
    "class X #(type T = int);\n"
    "  static int s;\n"
    "  static function int w(); T v; return $bits(v); endfunction\n"
    "endclass\n"
    "class Z #(int W = 1, type T = int);\n"
    "  static function int w(); T v; return $bits(v) * 10 + W; endfunction\n"
    "endclass\n"
    "logic [6:0] n;\n"
    "localparam logic [2:0] L = 1;\n"
    "pk::K k;\n";

struct PrefixPlace {
  std::string_view open;
  std::string_view use;
  std::string_view close;
};

constexpr PrefixPlace kPrefixPlaces[] = {
    {"module top;\n", "", "endmodule\n"},
    {"interface itf;\n", "", "endinterface\nmodule top; itf i(); endmodule\n"},
    {"program p;\n", "", "endprogram\nmodule top; p i(); endmodule\n"},
    {"module top;\nif (1) begin : b\n", "", "end\nendmodule\n"},
    {"package q;\n", "endpackage\nmodule top;\nimport q::*;\n", "endmodule\n"},
    {"", "module top;\n", "endmodule\n"},
};

std::string Declared(const PrefixPlace& place) {
  return std::string(kShared).append(place.open).append(kDeclarations);
}

void ExpectInEachPrefixPlace(std::string_view items, std::string_view use,
                             std::string_view printed) {
  for (const PrefixPlace& place : kPrefixPlaces) {
    const std::string kSource =
        Declared(place).append(items).append(place.use).append(use).append(
            place.close);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f), printed);
  }
}

TEST(ScopePrefixTypeRefArgumentSim, NamesTheStaticPropertyOfTheSpecialization) {
  ExpectInEachPrefixPlace(
      "function automatic void show();\n"
      "  X#(logic [6:0])::s = 5;\n"
      "  X#(int)::s = 1;\n"
      "  $display(\"%0d\", X#(type(n))::s);\n"
      "  X#(type(n))::s = 8;\n"
      "  X#(.T(type(L)))::s += 2;\n"
      "  $display(\"%0d %0d %0d\", X#(logic [6:0])::s, X#(int)::s,\n"
      "           X#(logic [2:0])::s);\n"
      "endfunction\n",
      "initial show();\n", "5\n8 1 2\n");
}

TEST(ScopePrefixTypeRefArgumentSim, TakesEachOperand) {
  ExpectInEachPrefixPlace(
      "function automatic void show();\n"
      "  $display(\"%0d %0d %0d\", X#(type(n))::w(),\n"
      "           X#(.T(type(n + 10'd0)))::w(), X#(type(L))::w());\n"
      "  $display(\"%0d %0d %0d\", X#(type(pk::w9))::w(),\n"
      "           X#(.T(type(pk::t)))::w(), X#(type(logic [5:0]))::w());\n"
      "  $display(\"%0d %0d %0d\", Z#(3, type(n))::w(),\n"
      "           Z#(.W(4), .T(type(L)))::w(), X#(.T())::w());\n"
      "  X#(pk::K)::s = 6;\n"
      "  $display(\"%0d\", X#(type(k))::s);\n"
      "endfunction\n",
      "initial show();\n", "7 10 3\n9 12 6\n73 34 32\n6\n");
}

TEST(ScopePrefixTypeRefArgumentSim, StandsInEachExpression) {
  ExpectInEachPrefixPlace(
      "function automatic int twice(int x); return x * 2; endfunction\n"
      "function automatic int back(); return X#(type(n))::w(); endfunction\n"
      "function automatic void show();\n"
      "  int a = X#(type(n))::w();\n"
      "  int b = 0;\n"
      "  for (int i = 0; i < X#(type(n))::w(); i++) b += 1;\n"
      "  repeat (X#(type(L))::w()) b += 10;\n"
      "  $display(\"%0d %0d %0d %0d\", a, b, twice(X#(type(n))::w()), "
      "back());\n"
      "  if (X#(type(n))::w() == 7) $display(\"if\");\n"
      "  case (7)\n"
      "    X#(type(n))::w(): $display(\"case\");\n"
      "    default: $display(\"default\");\n"
      "  endcase\n"
      "  a = X#(type(L))::w() == 3 ? X#(type(n))::w() + 1 : 0;\n"
      "  $display(\"%0d\", a);\n"
      "endfunction\n",
      "initial show();\n", "7 37 14 7\nif\ncase\n8\n");
}

TEST(ScopePrefixTypeRefArgumentSim, OperandIsTheLocalOrFormalThatHides) {
  ExpectInEachPrefixPlace(
      "function automatic int in_formal(byte n);\n"
      "  return X#(type(n))::w();\n"
      "endfunction\n"
      "function automatic void show();\n"
      "  begin\n"
      "    logic [1:0] n;\n"
      "    $display(\"%0d\", X#(type(n))::w());\n"
      "  end\n"
      "  $display(\"%0d %0d\", in_formal(1), X#(type(n))::w());\n"
      "endfunction\n",
      "initial show();\n", "2\n8 7\n");
}

TEST(ScopePrefixTypeRefArgumentSim, StandsInAClass) {
  ExpectInEachPrefixPlace(
      "class D;\n"
      "  logic [3:0] p;\n"
      "  int c;\n"
      "  function new(); c = X#(type(n))::w(); endfunction\n"
      "  function int own(); return X#(type(p))::w(); endfunction\n"
      "  function int self(); return X#(type(this.p))::w(); endfunction\n"
      "  static function int f(byte x); return X#(type(x))::w(); endfunction\n"
      "endclass\n"
      "class E #(type T = logic [4:0]);\n"
      "  T e;\n"
      "  function int own(); return X#(type(e))::w(); endfunction\n"
      "endclass\n",
      "D d = new;\n"
      "E e = new;\n"
      "E #(logic [9:0]) g = new;\n"
      "initial begin\n"
      "  $display(\"%0d %0d %0d %0d\", d.c, d.own(), d.self(), D::f(1));\n"
      "  $display(\"%0d %0d\", e.own(), g.own());\n"
      "end\n",
      "7 4 4 8\n5 10\n");
}

TEST(ScopePrefixTypeRefArgumentSim, NamesAPackagesClassAndANestedArgument) {
  ExpectInEachPrefixPlace(
      "function automatic void show();\n"
      "  pk::X#(logic [6:0])::s = 3;\n"
      "  X#(X#(logic [6:0]))::s = 4;\n"
      "  $display(\"%0d %0d %0d\", pk::X#(type(n))::s, pk::X#(type(n))::w(),\n"
      "           X#(X#(type(n)))::s);\n"
      "endfunction\n",
      "initial show();\n", "3 7 4\n");
}

constexpr PrefixPlace kProcedurePlaces[] = {kPrefixPlaces[0], kPrefixPlaces[1],
                                            kPrefixPlaces[3]};

TEST(ScopePrefixTypeRefArgumentSim, StandsInEachProcedure) {
  for (const PrefixPlace& place : kProcedurePlaces) {
    const std::string kSource =
        Declared(place)
            .append(
                "logic go = 0;\n"
                "int a, b;\n"
                "task tk(); #1 b = X#(type(n))::w(); endtask\n"
                "always @(posedge go) a = X#(type(n))::w();\n"
                "always_comb if (go) X#(logic [2:0])::s = X#(type(n))::w();\n"
                "initial begin\n"
                "  #1 go = 1;\n"
                "  #(X#(type(n))::w());\n"
                "  tk();\n"
                "  $display(\"%0t %0d %0d %0d\", $time, a, b,\n"
                "           X#(type(L))::s);\n"
                "end\n")
            .append(place.close);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f), "9 7 7 7\n");
  }
}

TEST(ScopePrefixTypeRefArgumentSim, StandsInAFinalProcedure) {
  for (const PrefixPlace& place : kProcedurePlaces) {
    const std::string kSource =
        Declared(place)
            .append("final $display(\"%0d\", X#(type(n))::w());\n")
            .append(place.close);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f), "");
    testing::internal::CaptureStdout();
    f.ctx.RunFinalBlocks();
    EXPECT_EQ(testing::internal::GetCapturedStdout(), "7\n");
  }
}

TEST(ScopePrefixTypeRefArgumentSim, EachInstanceTakesItsOwn) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          std::string(kShared).append(
              "module m #(int W = 2);\n"
              "logic [W-1:0] n;\n"
              "class X #(type T = int);\n"
              "  static function int w(); T v; return $bits(v); endfunction\n"
              "endclass\n"
              "function int show();\n"
              "  return X#(type(n))::w() * 10 + pk::X#(type(n + 1'b0))::w();\n"
              "endfunction\n"
              "endmodule\n"
              "module top;\n"
              "m #(3) a();\n"
              "m #(5) b();\n"
              "initial $display(\"%0d %0d\", a.show(), b.show());\n"
              "endmodule\n"),
          f),
      "33 55\n");
}

void ExpectPrefixOperandsJudged(const PrefixPlace& place,
                                std::string_view statement) {
  for (std::string_view operand : {"pk::w9", "nosuch", "top.u.hv"}) {
    std::string text(statement);
    text.replace(text.find('@'), 1, operand);
    const std::string kBefore =
        Declared(place).append("function automatic void show();\n");
    const std::string kSource = std::string(kBefore)
                                    .append(text)
                                    .append("\nendfunction\n")
                                    .append(place.use)
                                    .append(place.close);
    SCOPED_TRACE(kSource);
    SimFixture f;
    ElaborateSrc(kSource, f);
    const auto kLine =
        static_cast<uint32_t>(std::ranges::count(kBefore, '\n') + 1);
    EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                            "parameter value assignment for type parameter "
                            "'T' of 'X' does not name a type",
                            kLine, "6.20.3"),
              operand == "nosuch");
    EXPECT_EQ(
        ReportedError(f.diag.Diagnostics(),
                      "type operator argument uses a hierarchical reference, "
                      "which the type operator does not accept",
                      kLine, "6.23"),
        operand == "top.u.hv");
    const bool kLeavesAPackage =
        operand == "top.u.hv" && place.open == "package q;\n";
    EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top' that does not target the package itself or "
                            "an imported package",
                            kLine, "26.2"),
              kLeavesAPackage);
    EXPECT_EQ(f.diag.Diagnostics().size(),
              (operand == "pk::w9" ? 0U : 1U) + (kLeavesAPackage ? 1U : 0U));
  }
}

TEST(ScopePrefixTypeRefArgumentElab,
     OperandNamesATypeWithoutAHierarchicalName) {
  for (const PrefixPlace& place : kPrefixPlaces) {
    for (std::string_view statement :
         {"X#(type(@))::s = 1;", "$display(X#(.T(type(@)))::w());"}) {
      ExpectPrefixOperandsJudged(place, statement);
    }
  }
}

}  // namespace
