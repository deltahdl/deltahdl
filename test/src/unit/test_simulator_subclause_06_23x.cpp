#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

struct Place {
  std::string_view open;
  std::string_view use;
  std::string_view close;
};

constexpr Place kPlaces[] = {
    {"package q;\n", "endpackage\nmodule top;\nimport q::*;\n", "endmodule\n"},
    {"", "module top;\n", "endmodule\n"},
};

constexpr std::string_view kClass =
    "class C; typedef logic [6:0] u; static logic [4:0] s; endclass\n";

constexpr std::string_view kFormals =
    "(input var type(C::u) x, input var type(C::s) y);\n"
    "  var type(C::u) la;\n"
    "  var type(C::s) lb;\n"
    "  $display(\"%0d %0d %0d %0d\", $bits(x), $bits(y), $bits(la), "
    "$bits(lb));\n";

std::string Positions() {
  return std::string(
             "class P;\n"
             "  var type(C::u) a;\n"
             "  var type(C::s) b;\n"
             "  static var type(C::u) sa;\n"
             "  static var type(C::s) sb;\n"
             "  function void m")
      .append(kFormals)
      .append(
          "  endfunction\n"
          "endclass\n"
          "function automatic void f")
      .append(kFormals)
      .append(
          "endfunction\n"
          "task automatic t")
      .append(kFormals)
      .append("endtask\n");
}

TEST(ClassScopedTypeRefInScopeSim, TakesABareClassTypeOrStaticProperty) {
  for (const Place& place : kPlaces) {
    std::string text(place.open);
    text.append(kClass).append(Positions()).append(place.use);
    text.append(
        "  P p = new;\n"
        "  initial begin\n"
        "    $display(\"%0d %0d %0d %0d\", $bits(p.a), $bits(p.b), "
        "$bits(p.sa),\n"
        "             $bits(p.sb));\n"
        "    p.m(0, 0);\n"
        "    f(0, 0);\n"
        "    t(0, 0);\n"
        "  end\n");
    text.append(place.close);
    SCOPED_TRACE(text);
    SimFixture f;
    EXPECT_EQ(RunCapture(text, f), "7 5 7 5\n7 5 7 5\n7 5 7 5\n7 5 7 5\n");
  }
}

}  // namespace
