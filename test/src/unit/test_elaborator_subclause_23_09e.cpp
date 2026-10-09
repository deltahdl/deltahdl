// Tests for the §23.9 scope rules as they reach a name read in a concurrent
// assertion, a named sequence or a named property. §23.9 resolves an
// identifier referenced without a hierarchical path against the declarations
// its scope can reach, and §16.8 and §16.12 resolve a name in a sequence or
// property body other than a formal from the scope of the declaration, so a
// name those scopes do not declare is unresolved there as in a statement.
//
// The reads in statements are in test_elaborator_subclause_23_09a.cpp to
// 23_09d.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kUnresolved =
    "reference to unresolved identifier 'undeclared'";

// Elaborates `items`, module items of a module declaring `logic clk;` and
// `bit a;`, and asserts the §23.9 report stands on the line holding `anchor`.
void ExpectReportedIn(std::string_view items, std::string_view anchor) {
  ElabFixture f;
  std::string src = "module m;\n  logic clk;\n  bit a;\n" + std::string(items) +
                    "endmodule\n";
  Elaborate(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnresolved,
                            LineHolding(src, anchor), "23.9"));
}

TEST(AssertionReads, UndeclaredNameInAnAssertPropertyIsReported) {
  ExpectReportedIn("  assert property (@(posedge clk) undeclared);\n",
                   "assert property");
}

TEST(AssertionReads, UndeclaredNameInACoverSequenceIsReported) {
  ExpectReportedIn("  cover property (@(posedge clk) a ##1 undeclared);\n",
                   "cover property");
}

TEST(AssertionReads, UndeclaredNameInTheClockIsReported) {
  ExpectReportedIn("  assert property (@(posedge undeclared) a);\n",
                   "assert property");
}

TEST(AssertionReads, UndeclaredNameInASequenceBodyIsReported) {
  ExpectReportedIn(
      "  sequence s1;\n"
      "    a ##1 (undeclared == 1);\n"
      "  endsequence\n",
      "a ##1 (undeclared");
}

TEST(AssertionReads, UndeclaredNameInAPropertyBodyIsReported) {
  ExpectReportedIn(
      "  property p1;\n"
      "    @(posedge clk) a |=> undeclared;\n"
      "  endproperty\n",
      "a |=> undeclared");
}

// Every name below is declared where its read can reach it: a formal and a
// local of the declaration, a sequence and a property instantiated by name, a
// parameter, an enumeration constant, a function, a package's names reached
// by import and by `pkg::`, an interface instance's signal and `$` as a bound.
TEST(AssertionReads, NamesTheScopesDeclareAreAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "package pk;\n"
      "  bit pv;\n"
      "  sequence ps(x); x; endsequence\n"
      "endpackage\n"
      "interface bus; logic req; endinterface\n"
      "module m;\n"
      "  import pk::*;\n"
      "  logic clk;\n"
      "  bit a, b;\n"
      "  int data;\n"
      "  parameter int N = 2;\n"
      "  typedef enum {IDLE, BUSY} st_t;\n"
      "  st_t st;\n"
      "  bus u();\n"
      "  function automatic bit f(bit x); return x; endfunction\n"
      "  sequence s1(x, lo, hi);\n"
      "    int v;\n"
      "    (x, v = data) ##[lo:hi] (data == v);\n"
      "  endsequence\n"
      "  property p1(y);\n"
      "    @(posedge clk) y |=> s1(b, 1, $);\n"
      "  endproperty\n"
      "  assert property (p1(a));\n"
      "  assert property (@(posedge clk) a ##N (st == BUSY) ##1 f(b));\n"
      "  assert property (@(posedge clk) pv ##1 pk::pv ##1 ps(u.req));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.9.2: an assignment pattern's member keys name members of its type, not
// objects of the scope, so a pattern passed as an actual reads none of them,
// whether written first or after a comma, while the names it reads as
// values, a ternary's and a concatenation's among them, still resolve
// (#5762).
TEST(AssertionReads, APatternsMemberKeysAreNoReads) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk; bit x, y, z;\n"
      "  typedef struct packed { logic a, b, c; } trio_t;\n"
      "  property p(trio_t s); @(posedge clk) s.a; endproperty\n"
      "  assert property (p('{a: x, b: y ? z : x, c: {y}}));\n"
      "  assert property (@(posedge clk) {x, y} == 2'b01);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionReads, AnUndeclaredValueInAPatternIsReported) {
  ExpectReportedIn(
      "  typedef struct packed { logic a, b; } pair_t;\n"
      "  property p(pair_t s); @(posedge clk) s.a; endproperty\n"
      "  assert property (p('{a: undeclared, default: 1'b0}));\n",
      "assert property");
}

}  // namespace
