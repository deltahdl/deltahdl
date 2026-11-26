#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr std::string_view kPackage =
    "package pq;\n"
    "  class P; rand int a; logic [6:0] n; endclass\n"
    "endpackage\n";

constexpr std::string_view kClasses =
    "class X #(type T = int);\n"
    "  static function int w(); T v; return $bits(v); endfunction\n"
    "endclass\n"
    "class B; logic [6:0] n; endclass\n"
    "class O; rand int a, f, g; logic [6:0] n; endclass\n"
    "class E extends B; rand int a; endclass\n"
    "class Q #(type T = int); rand int a; T n; endclass\n"
    "logic [4:0] n, s;\n";

struct Place {
  std::string_view open;
  std::string_view use;
  std::string_view close;
};

constexpr Place kPlaces[] = {
    {"module top;\n", "", "endmodule\n"},
    {"interface itf;\n", "", "endinterface\nmodule top; itf i(); endmodule\n"},
    {"program p;\n", "", "endprogram\nmodule top; p i(); endmodule\n"},
    {"package q;\n", "endpackage\nmodule top;\nimport q::*;\n", "endmodule\n"},
    {"", "module top;\n", "endmodule\n"},
};

void ExpectEachPlacePrints(std::string_view declared, std::string_view run,
                           std::string_view printed) {
  for (const Place& place : kPlaces) {
    std::string text(kPackage);
    text.append(place.open).append(kClasses).append(declared);
    text.append(place.use).append(run).append(place.close);
    SCOPED_TRACE(text);
    SimFixture f;
    EXPECT_EQ(RunCapture(text, f), printed);
  }
}

TEST(InlinePrefixTypeRefObjectSim, ObjectsNameHidesTheProceduresName) {
  ExpectEachPlacePrints(
      "task automatic t();\n"
      "  O o1 = new, o2 = new, o3 = new;\n"
      "  logic [2:0] n = 0;\n"
      "  logic [1:0] m = 0;\n"
      "  void'(o1.randomize() with {\n"
      "    a == X#(type(n))::w();\n"
      "    f == X#(type(this.n))::w();\n"
      "    g == X#(type(local::n))::w();\n"
      "  });\n"
      "  void'(o2.randomize() with (a) {\n"
      "    a == X#(type(n))::w() * 100 + X#(type(m))::w() * 10 +\n"
      "         X#(type(s))::w();\n"
      "  });\n"
      "  void'(o3.randomize() with (a, n) { a == X#(type(n))::w(); });\n"
      "  $display(\"%0d %0d %0d %0d %0d\", o1.a, o1.f, o1.g, o2.a, o3.a);\n"
      "endtask\n",
      "initial t();\n", "7 7 3 325 7\n");
}

TEST(InlinePrefixTypeRefObjectSim, MethodsObjectNameHidesItsLocal) {
  ExpectEachPlacePrints(
      "class C;\n"
      "  rand int a;\n"
      "  logic [6:0] n;\n"
      "  function int self();\n"
      "    logic [2:0] n;\n"
      "    void'(this.randomize() with { a == X#(type(n))::w(); });\n"
      "    return a;\n"
      "  endfunction\n"
      "  function int own();\n"
      "    logic [2:0] n;\n"
      "    void'(randomize() with { a == X#(type(n))::w() + 1; });\n"
      "    return a;\n"
      "  endfunction\n"
      "endclass\n",
      "C c = new;\n"
      "initial $display(\"%0d %0d\", c.self(), c.own());\n",
      "7 8\n");
}

TEST(InlinePrefixTypeRefObjectSim, TakesTheMemberOfEachKindOfClass) {
  ExpectEachPlacePrints(
      "task automatic t();\n"
      "  E e = new;\n"
      "  pq::P p = new;\n"
      "  Q#(logic [6:0]) q7 = new;\n"
      "  Q#(logic [5:0]) q6 = new;\n"
      "  logic [2:0] n = 0;\n"
      "  void'(e.randomize() with { a == X#(type(n))::w(); });\n"
      "  void'(p.randomize() with { a == X#(type(n))::w(); });\n"
      "  void'(q7.randomize() with { a == X#(type(n))::w(); });\n"
      "  void'(q6.randomize() with { a == X#(type(n))::w(); });\n"
      "  $display(\"%0d %0d %0d %0d\", e.a, p.a, q7.a, q6.a);\n"
      "endtask\n",
      "initial t();\n", "7 7 7 6\n");
}

}  // namespace
