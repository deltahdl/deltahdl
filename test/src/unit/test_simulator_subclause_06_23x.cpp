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

constexpr std::string_view kClasses =
    "class C; typedef logic [6:0] u; static logic [4:0] s; endclass\n"
    "class W #(type T = int); typedef T u; static T s; endclass\n";

std::string Formals(std::string_view type, std::string_view value) {
  return std::string("(input var type(")
      .append(type)
      .append(") x, input var type(")
      .append(value)
      .append(") y);\n  var type(")
      .append(type)
      .append(") la;\n  var type(")
      .append(value)
      .append(
          ") lb;\n"
          "  $display(\"%0d %0d %0d %0d\", $bits(x), $bits(y), $bits(la), "
          "$bits(lb));\n");
}

std::string Positions(std::string_view type, std::string_view value) {
  const std::string kFormals = Formals(type, value);
  return std::string("class P;\n  var type(")
      .append(type)
      .append(") a;\n  var type(")
      .append(value)
      .append(") b;\n  static var type(")
      .append(type)
      .append(") sa;\n  static var type(")
      .append(value)
      .append(") sb;\n  function void m")
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

void ExpectInEachPlaceAndPosition(std::string_view type, std::string_view value,
                                  std::string_view bits) {
  std::string printed;
  for (int line = 0; line < 4; ++line) printed.append(bits).append("\n");
  for (const Place& place : kPlaces) {
    std::string text(place.open);
    text.append(kClasses).append(Positions(type, value)).append(place.use);
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
    EXPECT_EQ(RunCapture(text, f), printed);
  }
}

TEST(ClassScopedTypeRefInScopeSim, TakesABareClassTypeOrStaticProperty) {
  ExpectInEachPlaceAndPosition("C::u", "C::s", "7 5 7 5");
}

TEST(ClassScopedTypeRefInScopeSim, TakesASpecializationsTypeOrStaticProperty) {
  ExpectInEachPlaceAndPosition("W#(byte)::u", "W#(byte)::s", "8 8 8 8");
}

TEST(ClassScopedTypeRefInScopeSim, SpecializationArgumentDecidesTheType) {
  ExpectInEachPlaceAndPosition("W#(logic [6:0])::u", "W#(logic [6:0])::s",
                               "7 7 7 7");
}

}  // namespace
