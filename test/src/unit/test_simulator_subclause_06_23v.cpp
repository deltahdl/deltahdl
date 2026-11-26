#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr std::string_view kOutside =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  logic [8:0] w9;\n"
    "  class K; int m = 5; endclass\n"
    "endpackage\n"
    "package q;\n"
    "  class C2 #(int W = 1, type T = int); typedef T u; endclass\n"
    "endpackage\n"
    "class C #(int W = 1, type T = int); typedef T u; endclass\n";

constexpr std::string_view kInside =
    "class C3 #(int W = 1, type T = int); typedef T u; endclass\n"
    "logic [6:0] n;\n"
    "localparam logic [2:0] L = 1;\n"
    "pk::K k;\n";

constexpr std::string_view kScopes[][2] = {
    {"module top;\n", "endmodule\n"},
    {"interface itf;\n", "endinterface\nmodule top; itf i(); endmodule\n"},
    {"program p;\n", "endprogram\nmodule top; p i(); endmodule\n"},
};

void ExpectEachScopePrints(std::string_view body, std::string_view printed) {
  for (const auto& [open, close] : kScopes) {
    std::string text(kOutside);
    text.append(open).append(kInside).append(body).append(close);
    SCOPED_TRACE(text);
    SimFixture f;
    EXPECT_EQ(RunCapture(text, f), printed);
  }
}

TEST(TypeOperatorOfSpecializationTypedefSim, TakesTheArgumentsType) {
  ExpectEachScopePrints(
      "var type(C#(1, type(n))::u) b;\n"
      "var type(q::C2#(1, type(n))::u) c;\n"
      "var type(C3#(1, type(n))::u) d;\n"
      "initial $display(\"%0d %0d %0d\", $bits(b), $bits(c), $bits(d));\n",
      "7 7 7\n");
}

TEST(TypeOperatorOfSpecializationTypedefSim,
     StandsInAFormalALocalAndAProperty) {
  ExpectEachScopePrints(
      "function int f(var type(C#(1, type(n))::u) x);\n"
      "  return $bits(x);\n"
      "endfunction\n"
      "task t(output int w, input var type(C3#(1, type(n))::u) y);\n"
      "  w = $bits(y);\n"
      "endtask\n"
      "class D; var type(C3#(1, type(n))::u) p; endclass\n"
      "initial begin\n"
      "  var type(C#(1, type(n))::u) l;\n"
      "  automatic D o = new;\n"
      "  int w;\n"
      "  t(w, 0);\n"
      "  $display(\"%0d %0d %0d %0d\", f(0), w, $bits(l), $bits(o.p));\n"
      "end\n",
      "7 7 7 7\n");
}

TEST(TypeOperatorOfSpecializationTypedefSim, TakesEachOperand) {
  ExpectEachScopePrints(
      "var type(C#(1, type(n + 10'd0))::u) e1;\n"
      "var type(C#(.T(type(L)))::u) e2;\n"
      "var type(C#(1, type(pk::w9))::u) e3;\n"
      "var type(C#(.W(2), .T(type(pk::t)))::u) e4;\n"
      "var type(C#(1, type(logic [5:0]))::u) e5;\n"
      "var type(C#(1, type(k))::u) e6;\n"
      "initial begin\n"
      "  e6 = new;\n"
      "  $display(\"%0d %0d %0d %0d %0d %0d\",\n"
      "           $bits(e1), $bits(e2), $bits(e3), $bits(e4), $bits(e5),\n"
      "           e6.m);\n"
      "end\n",
      "10 3 9 12 6 5\n");
}

}  // namespace
