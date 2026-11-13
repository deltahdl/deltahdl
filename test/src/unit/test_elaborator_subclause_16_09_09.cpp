#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kSequenceForBoolean =
    "a sequence stands where the grammar admits only an expression_or_dist";

struct LeftOperandPair {
  const char* outside;
  const char* items;
  const char* bad;
  const char* good;
};

std::string Filled(const std::string& text, const std::string& form) {
  std::string out = text;
  size_t at = out.find("@@");
  if (at != std::string::npos) out.replace(at, 2, form);
  return out;
}

std::string LeftOperandSource(const LeftOperandPair& pair,
                              const std::string& form) {
  return Filled(pair.outside, form) +
         "module m;\n"
         "  bit clk, x, a, b, c;\n"
         "  sequence s; a ##1 b; endsequence\n"
         "  sequence s2(p, q); p ##1 q; endsequence\n"
         "  property pp; a ##1 b; endproperty\n"
         "  function bit f(bit y); return y; endfunction\n"
         "  " +
         Filled(pair.items, form) + "\nendmodule\n";
}

constexpr const char* kModuleAssert =
    "assert property (@(posedge clk) @@ throughout (c ##1 c));";

constexpr const char* kPackage =
    "package p;\n"
    "  sequence s; 1 ##1 1; endsequence\n"
    "  localparam bit B = 1;\n"
    "endpackage\n";

constexpr const char* kChild =
    "module u;\n"
    "  bit v;\n"
    "  sequence s; 1 ##1 1; endsequence\n"
    "endmodule\n";

const LeftOperandPair kPairs[] = {
    {"", kModuleAssert, "s", "s.triggered"},
    {"", kModuleAssert, "s", "s.matched"},
    {"", kModuleAssert, "s", "x dist {0 := 1, 1 := 1}"},
    {"", "sequence q; @@ throughout (c ##1 c); endsequence", "s", "x"},
    {"", "property r; @@ throughout (c ##1 c); endproperty", "s", "x"},
    {"", kModuleAssert, "s2(a, b)", "f(a)"},
    {"", kModuleAssert, "pp", "x"},
    {"",
     "sequence g(@@); w throughout (c ##1 c); endsequence\n"
     "  cover property (@(posedge clk) g(a));",
     "sequence w", "w"},
    {kPackage, kModuleAssert, "p::s", "p::B"},
    {kChild, "u u1();\n  assert property (@(posedge clk) @@ throughout c);",
     "u1.s", "u1.v"},
    {"", "always @(posedge clk) assert property (@@ throughout (c ##1 c));",
     "s", "x"},
    {"", "cover sequence (@(posedge clk) @@ throughout (c ##1 c));", "s", "x"},
    {"interface ifc(input logic clk);\n"
     "  bit a, b, c, x;\n"
     "  sequence s; a ##1 b; endsequence\n"
     "  assert property (@(posedge clk) @@ throughout (c ##1 c));\n"
     "endinterface\n",
     "ifc i(clk);", "s", "x"},
    {"checker ck(bit clk, bit a, bit b, bit c, bit x);\n"
     "  sequence s; a ##1 b; endsequence\n"
     "  assert property (@(posedge clk) @@ throughout (c ##1 c));\n"
     "endchecker\n",
     "ck k(clk, a, b, c, x);", "s", "x"},
};

uint32_t LeftOperandLine(const std::string& src, const std::string& form) {
  return LineHolding(src, form + " throughout");
}

TEST(ThroughoutLeftOperand,
     DISABLED_ASequenceOrPropertyInstanceOnTheLeftIsReported) {
  for (const LeftOperandPair& pair : kPairs) {
    SCOPED_TRACE(pair.bad);
    const std::string kSrc = LeftOperandSource(pair, pair.bad);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    const std::string kName =
        std::string(pair.bad) == "sequence w" ? "w" : pair.bad;
    uint32_t line = LeftOperandLine(kSrc, kName);
    ASSERT_NE(line, 0u);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kSequenceForBoolean, line,
                              "A.2.10"));
  }
}

TEST(ThroughoutLeftOperand, TheNearestExpressionOnTheLeftIsAccepted) {
  for (const LeftOperandPair& pair : kPairs) {
    SCOPED_TRACE(pair.good);
    const std::string kSrc = LeftOperandSource(pair, pair.good);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

}  // namespace
