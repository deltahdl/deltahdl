#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr std::string_view kOtherPackage =
    "package pk;\n"
    "  class X #(type T = int);\n"
    "    T v;\n"
    "    function int w(); return $bits(v); endfunction\n"
    "  endclass\n"
    "endpackage\n";

constexpr std::string_view kClasses =
    "class X #(type T = int);\n"
    "  T v;\n"
    "  function int w(); return $bits(v); endfunction\n"
    "endclass\n"
    "class Z #(int W = 1, type T = int);\n"
    "  T v;\n"
    "  function int w(); return $bits(v) * 10 + W; endfunction\n"
    "endclass\n"
    "localparam int N = 5;\n";

struct DeclaringScope {
  std::string_view open;
  std::string_view close;
  std::string_view import;
  std::string_view name;
};

constexpr DeclaringScope kDeclaringScopes[] = {
    {"package q;\n", "endpackage\n", "", "q::"},
    {"package q;\n", "endpackage\n", "import q::*;\n", ""},
    {"", "", "", ""},
};

std::string Named(std::string_view text, std::string_view name) {
  std::string named(text);
  for (std::size_t at = named.find('@'); at != std::string::npos;
       at = named.find('@')) {
    named.replace(at, 1, name);
  }
  return named;
}

void ExpectPrinted(std::string_view variables, std::string_view use,
                   std::string_view printed) {
  for (const DeclaringScope& scope : kDeclaringScopes) {
    const std::string kSource = std::string(kOtherPackage)
                                    .append(scope.open)
                                    .append(kClasses)
                                    .append(variables)
                                    .append(scope.close)
                                    .append("module top;\n")
                                    .append(scope.import)
                                    .append(Named(use, scope.name))
                                    .append("endmodule\n");
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f), printed);
  }
}

TEST(ScopeVariableNewSim, InitializerConstructsTheSpecialization) {
  ExpectPrinted(
      "X #(logic [6:0]) a = new;\n"
      "Z #(3, logic [1:0]) b = new;\n"
      "Z #(.T(logic [1:0]), .W(4)) c = new;\n"
      "X #(logic [N-1:0]) d = new;\n"
      "pk::X #(logic [6:0]) e = new;\n"
      "X g = new;\n",
      "initial begin\n"
      "  $display(\"%0d %0d %0d\", @a.w(), $bits(@a.v), @b.w());\n"
      "  $display(\"%0d %0d %0d %0d\", @c.w(), @d.w(), @e.w(), @g.w());\n"
      "end\n",
      "7 7 23\n24 5 7 32\n");
}

TEST(ScopeVariableNewSim, ProcedureConstructsTheSpecialization) {
  ExpectPrinted(
      "X #(logic [6:0]) a;\n"
      "Z #(3, logic [1:0]) b;\n"
      "Z #(.T(logic [1:0]), .W(4)) c;\n"
      "X #(logic [N-1:0]) d;\n"
      "pk::X #(logic [6:0]) e;\n"
      "X g;\n",
      "initial begin\n"
      "  @a = new;\n"
      "  @b = new;\n"
      "  @c = new;\n"
      "  @d = new;\n"
      "  @e = new;\n"
      "  @g = new;\n"
      "  $display(\"%0d %0d %0d\", @a.w(), $bits(@a.v), @b.w());\n"
      "  $display(\"%0d %0d %0d %0d\", @c.w(), @d.w(), @e.w(), @g.w());\n"
      "end\n",
      "7 7 23\n24 5 7 32\n");
}

}  // namespace
