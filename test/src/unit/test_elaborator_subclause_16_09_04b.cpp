#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_marked_reports.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kNestReport =
    "a global clocking future sampled value function may not stand in the "
    "argument of ";

void ExpectNestReports(const MarkedSource& marked) {
  ExpectMarkedReports(marked, kNestReport, "16.9.4");
}

std::string GlobalModule(const std::string& items) {
  return "module m;\n"
         "  bit clk, a, b, c;\n"
         "  logic [3:0] v;\n"
         "  global clocking @(posedge clk); endclocking\n" +
         items + "endmodule\n";
}

size_t ErrorsOnLine(const std::vector<Diagnostic>& diags, uint32_t line) {
  size_t count = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError && diag.loc.line == line) {
      ++count;
    }
  }
  return count;
}

TEST(FutureGclkNesting, EachFutureFunctionIsNamedAsTheOuterOne) {
  const char* const kOuter[] = {"$future_gclk", "$rising_gclk", "$falling_gclk",
                                "$steady_gclk", "$changing_gclk"};
  for (std::string outer : kOuter) {
    SCOPED_TRACE(outer);
    std::string inner =
        outer == "$steady_gclk" ? "$future_gclk" : "$steady_gclk";
    std::string items = "  a1: assert property (@(posedge clk) ";
    items += outer;
    items += "(";
    items += inner;
    items += "(a)));\n  a2: assert property (@(posedge clk) ";
    items += outer;
    items += "(a));\n";
    std::string src = GlobalModule(items);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string(kNestReport) + outer,
                              LineHolding(src, "a1:"), "16.9.4"));
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, "a2:")));
  }
}

TEST(FutureGclkNesting, EachFutureFunctionIsReportedAsTheInnerOne) {
  ExpectNestReports(
      {"inner functions",
       GlobalModule("  a1: assert property (@(posedge clk) "
                    "$rising_gclk($future_gclk(a)));\n"
                    "  a2: assert property (@(posedge clk) "
                    "$rising_gclk($rising_gclk(a)));\n"
                    "  a3: assert property (@(posedge clk) "
                    "$rising_gclk($falling_gclk(a)));\n"
                    "  a4: assert property (@(posedge clk) "
                    "$rising_gclk($steady_gclk(a)));\n"
                    "  a5: assert property (@(posedge clk) "
                    "$rising_gclk($changing_gclk(a)));\n"
                    "  b1: assert property (@(posedge clk) "
                    "$future_gclk($past_gclk(a)));\n"
                    "  b2: assert property (@(posedge clk) "
                    "$rising_gclk($fell_gclk(a)));\n"
                    "  b3: assert property (@(posedge clk) $rising_gclk(a) &&"
                    " $falling_gclk(b));\n"),
       {"a1:", "a2:", "a3:", "a4:", "a5:"},
       {"b1:", "b2:", "b3:"}});
}

TEST(FutureGclkNesting, AnInnerCallUnderAnyOperatorIsReportedOnce) {
  std::string src = GlobalModule(
      "  a1: assert property (@(posedge clk) $falling_gclk(a && "
      "$steady_gclk(b)));\n"
      "  a2: assert property (@(posedge clk) "
      "$falling_gclk(!$steady_gclk(b)));\n"
      "  a3: assert property (@(posedge clk) $falling_gclk(a ? $steady_gclk(b)"
      " : c));\n"
      "  a4: assert property (@(posedge clk) $steady_gclk({a, "
      "$future_gclk(b)}));\n"
      "  a5: assert property (@(posedge clk) "
      "$rising_gclk($countones($future_gclk(v)) == 1));\n"
      "  b1: assert property (@(posedge clk) $falling_gclk(a && "
      "$past_gclk(b)));\n"
      "  b2: assert property (@(posedge clk) $steady_gclk({a, b}));\n"
      "  b3: assert property (@(posedge clk) $rising_gclk($countones(v) =="
      " 1));\n");
  ExpectNestReports({"operand positions",
                     src,
                     {"a1:", "a2:", "a3:", "a4:", "a5:"},
                     {"b1:", "b2:", "b3:"}});
  ElabFixture f;
  ElaborateSrc(src, f);
  for (const char* label : {"a1:", "a2:", "a3:", "a4:", "a5:"}) {
    EXPECT_EQ(ErrorsOnLine(f.diag.Diagnostics(), LineHolding(src, label)), 1u)
        << label;
  }
}

TEST(FutureGclkNesting, NestingIsReportedInEveryAssertionStatement) {
  ExpectNestReports(
      {"assertion statements",
       GlobalModule(
           "  a1: assume property (@(posedge clk)"
           " $changing_gclk($steady_gclk(a)));\n"
           "  a2: cover property (@(posedge clk)"
           " $changing_gclk($steady_gclk(b)));\n"
           "  a3: restrict property (@(posedge clk)"
           " $changing_gclk($steady_gclk(c)));\n"
           "  a4: cover sequence (@(posedge clk)"
           " $rising_gclk($steady_gclk(a)));\n"
           "  always @(posedge clk) begin\n"
           "    a5: assert property ($changing_gclk($steady_gclk(c)));\n"
           "    b5: assert property ($changing_gclk(c));\n"
           "  end\n"
           "  b1: assume property (@(posedge clk) $changing_gclk(a));\n"
           "  b2: cover property (@(posedge clk) $changing_gclk(b));\n"
           "  b3: restrict property (@(posedge clk) $changing_gclk(c));\n"
           "  b4: cover sequence (@(posedge clk) $rising_gclk(a));\n"),
       {"a1:", "a2:", "a3:", "a4:", "a5:"},
       {"b1:", "b2:", "b3:", "b4:", "b5:"}});
}

TEST(FutureGclkNesting, NestingIsReportedInEveryDesignElement) {
  ExpectNestReports(
      {"interface, program and checker",
       "interface ifc(input logic clk, a);\n"
       "  a1: assert property (@(posedge clk) $rising_gclk($steady_gclk(a)));\n"
       "  b1: assert property (@(posedge clk) $rising_gclk(a));\n"
       "endinterface\n"
       "program pg(input logic clk, a);\n"
       "  a2: assert property (@(posedge clk) "
       "$falling_gclk($future_gclk(a)));\n"
       "  b2: assert property (@(posedge clk) $falling_gclk(a));\n"
       "endprogram\n"
       "checker ck(bit clk, bit a);\n"
       "  a3: assert property (@(posedge clk) "
       "$steady_gclk($changing_gclk(a)));\n"
       "  b3: assert property (@(posedge clk) $steady_gclk(a));\n"
       "endchecker\n"
       "module m;\n"
       "  bit clk, a;\n"
       "  global clocking @(posedge clk); endclocking\n"
       "  ifc i(clk, a);\n"
       "  pg p(clk, a);\n"
       "  ck k(clk, a);\n"
       "endmodule\n",
       {"a1:", "a2:", "a3:"},
       {"b1:", "b2:", "b3:"}});
}

TEST(FutureGclkNesting, NestingInAModuleDeclarationIsReportedThere) {
  ExpectNestReports(
      {"module declarations",
       GlobalModule(
           "  sequence s1; @(posedge clk) $steady_gclk($rising_gclk(a));"
           " endsequence\n"
           "  property p1; @(posedge clk) $future_gclk($rising_gclk(a));"
           " endproperty\n"
           "  sequence s2; @(posedge clk) $steady_gclk(a); endsequence\n"
           "  property p2(x); @(posedge clk) $rising_gclk(x); endproperty\n"
           "  a1: assert property (s1);\n"
           "  a2: assert property (p1);\n"
           "  a3: assert property (s2);\n"
           "  a4: assert property (p2(a));\n"),
       {"sequence s1;", "property p1;"},
       {"sequence s2;", "property p2(", "a3:", "a4:"}});
}

TEST(FutureGclkNesting, DISABLED_NestingInAModuleDeclarationIsReportedOnce) {
  std::string src = GlobalModule(
      "  sequence s1; @(posedge clk) $steady_gclk($rising_gclk(a));"
      " endsequence\n"
      "  property p1; @(posedge clk) $future_gclk($rising_gclk(a));"
      " endproperty\n"
      "  a1: assert property (s1);\n"
      "  a2: assert property (p1);\n");
  ElabFixture f;
  ElaborateSrc(src, f);
  for (const char* decl : {"sequence s1;", "property p1;"}) {
    EXPECT_EQ(ErrorsOnLine(f.diag.Diagnostics(), LineHolding(src, decl)), 1u)
        << decl;
  }
}

TEST(FutureGclkNesting, DISABLED_NestingOutsideADesignElementIsReported) {
  ExpectNestReports(
      {"package and compilation unit",
       "package pk;\n"
       "  sequence ps(x); $steady_gclk($rising_gclk(x)); endsequence\n"
       "  property pq(x); $future_gclk($rising_gclk(x)); endproperty\n"
       "  sequence pr(x); $steady_gclk(x); endsequence\n"
       "endpackage\n"
       "sequence us(x); $falling_gclk($changing_gclk(x)); endsequence\n"
       "sequence ur(x); $falling_gclk(x); endsequence\n"
       "module m;\n"
       "  bit clk, a;\n"
       "  global clocking @(posedge clk); endclocking\n"
       "  c1: assert property (@(posedge clk) pk::ps(a));\n"
       "  c2: assert property (@(posedge clk) pk::pq(a));\n"
       "  c3: assert property (@(posedge clk) pk::pr(a));\n"
       "  c4: assert property (@(posedge clk) us(a));\n"
       "  c5: assert property (@(posedge clk) ur(a));\n"
       "endmodule\n",
       {"sequence ps(", "property pq(", "sequence us("},
       {"sequence pr(", "sequence ur(", "c3:", "c5:"}});
}

TEST(FutureGclkNesting, DISABLED_NestingInAGenerateBlockIsReported) {
  ExpectNestReports(
      {"generate blocks",
       GlobalModule(
           "  if (1) begin : h\n"
           "    a1: assert property (@(posedge clk)"
           " $future_gclk($steady_gclk(a)));\n"
           "    b1: assert property (@(posedge clk) $future_gclk(a));\n"
           "    sequence gs; @(posedge clk) $steady_gclk($falling_gclk(b));"
           " endsequence\n"
           "    a3: assert property (gs);\n"
           "  end\n"
           "  for (genvar i = 0; i < 1; i++) begin : g\n"
           "    a2: assert property (@(posedge clk)"
           " $rising_gclk($steady_gclk(a)));\n"
           "    b2: assert property (@(posedge clk) $rising_gclk(a));\n"
           "  end\n"),
       {"a1:", "a2:", "sequence gs;"},
       {"b1:", "b2:"}});
}

TEST(FutureGclkNesting,
     DISABLED_AFutureActualPutInsideAFutureFunctionIsReported) {
  ExpectNestReports(
      {"actual arguments",
       GlobalModule(
           "  property q(x); $rising_gclk(x); endproperty\n"
           "  sequence r(x); $falling_gclk(x); endsequence\n"
           "  d1: assert property (@(posedge clk) q($steady_gclk(a)));\n"
           "  d2: assert property (@(posedge clk) r($future_gclk(b)));\n"
           "  e1: assert property (@(posedge clk) q(a));\n"
           "  e2: assert property (@(posedge clk) r($past_gclk(b)));\n"),
       {"d1:", "d2:"},
       {"e1:", "e2:"}});
}

}  // namespace
