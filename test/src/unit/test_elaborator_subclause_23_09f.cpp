// Tests for the §23.9 scope rules as they reach a name read in a method of a
// class. §23.9 resolves a name read in a task or function upward through the
// scopes that enclose it: the method's own formals and declarations, its class
// with the classes it extends (§8.13) and the class's parameters, and the
// scope that declares the class with what it imports. A name none of them
// declares is unresolved there as in a module's own subroutine.
//
// The reads in a module's statements are in
// test_elaborator_subclause_23_09a.cpp to 23_09d, and those of assertions in
// 23_09e.

#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §23.9: a name a class method reads that nothing declares, on the right of
// an assignment or in a condition, is unresolved.
TEST(ClassMethodScopeRules, ReadOfUndeclaredNameIsUnresolved) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  class k;\n"
      "    int y;\n"
      "    function void f; y = nosuch; endfunction\n"
      "    task g; if (other) y = 1; endtask\n"
      "  endclass\n"
      "endmodule\n",
      f);
  for (auto [line, name] :
       std::initializer_list<std::pair<uint32_t, const char*>>{{4u, "nosuch"},
                                                               {5u, "other"}}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("reference to unresolved identifier '") + name + "'", line,
        "23.9"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// §23.9 with §8.13 and §26.3: a class method reads its formals and locals,
// its class's properties, parameters, type parameters and enumeration
// members, those of the class it extends, and the names of the module that
// declares the class, its ports, parameters and type parameters and the package
// it imports among them; an enumeration member written `S[2]` gives S0 and S1
// (§6.19.2), and a nested class's method reads its outer class's parameter.
TEST(ClassMethodScopeRules, ReadsOfNamesItsScopesDeclareResolve) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  int pv;\n"
      "  typedef enum {RED, GREEN} col_t;\n"
      "endpackage\n"
      "class base;\n"
      "  int b;\n"
      "  static int sb;\n"
      "endclass\n"
      "module t #(parameter int MQ = 1, parameter type MT = int)\n"
      "    (input logic clk);\n"
      "  import pk::*;\n"
      "  int mv;\n"
      "  localparam int MP = 3;\n"
      "  typedef enum {LO, HI} lvl_t;\n"
      "  class k #(int W = 4, type T = int) extends base;\n"
      "    typedef enum {ONE, TWO} n_t;\n"
      "    enum {A, B} e;\n"
      "    int y;\n"
      "    int q[$];\n"
      "    localparam int KP = 2;\n"
      "    function int f(int arg);\n"
      "      int loc;\n"
      "      loc = arg + y + b + sb + W + KP + mv + MP + pv;\n"
      "      y = loc + RED + LO + ONE + A + $bits(T);\n"
      "      foreach (q[i]) y = q[i];\n"
      "      y = MQ + clk + $bits(MT) + S0 + S1;\n"
      "      return loc;\n"
      "    endfunction\n"
      "    typedef enum {S[2]} s_t;\n"
      "    class inner;\n"
      "      int z;\n"
      "      function void g; z = KP; endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "  k #(8) h = new;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
