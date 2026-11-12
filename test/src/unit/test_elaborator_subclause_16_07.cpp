#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SequenceExprElaboration, CycleDelayConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b ##2 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceExprElaboration, RangedDelayConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, req, gnt;\n"
      "  sequence req_gnt;\n"
      "    @(posedge clk) req ##[1:5] gnt;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceExprElaboration, ParenthesizedSequenceWithRepetitionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s;\n"
      "    @(posedge clk) (a ##1 b)[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceExprElaboration, UnboundedDelayWithDollarElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, req, ack;\n"
      "  property p;\n"
      "    @(posedge clk) req |-> ##[0:$] ack;\n"
      "  endproperty\n"
      "  assert property (p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CycleDelayElaboration, ParameterAndActualBoundsAreChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  localparam int LO = 3, HI = 1, NEG = -1;\n"
      "  sequence s(int d);\n"
      "    a ##d b;\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) a ##[LO:HI] b);\n"
      "  a2: assert property (@(posedge clk) s(NEG));\n"
      "  a3: assert property (@(posedge clk) s(LO));\n"
      "  a4: assert property (@(posedge clk) a ##[HI:LO] b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the maximum of a cycle delay range shall be no "
                            "less than its minimum",
                            7, "16.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a cycle delay shall be 0 or greater", 5, "16.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "the maximum of a cycle delay range", 10, "16.7"));
}

TEST(CycleDelayElaboration, ABoundLedByALiteralIsFoldedWhole) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  a1: assert property (@(posedge clk) a ##[2+1:1] b);\n"
      "  a2: assert property (@(posedge clk) a ##[1+1:3] b);\n"
      "  sequence s;\n"
      "    a ##[1:4-5] b;\n"
      "  endsequence\n"
      "  a3: assert property (@(posedge clk) s);\n"
      "  a4: assert property (@(posedge clk) a ##[1:5-4] b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the maximum of a cycle delay range shall be no "
                            "less than its minimum",
                            3, "16.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "the maximum of a cycle delay range", 4, "16.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a cycle delay shall be 0 or greater", 6, "16.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "a cycle delay shall be 0 or greater", 9, "16.7"));
}

const char kNotInteger[] = "be an integer";
const char kNotConstant[] = "be a constant expression";

std::string DelayBench(const std::string& items,
                       const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0, a = 1, b = 1;\n"
         "  int n;\n"
         "  const int C = 2;\n"
         "  localparam int P = 2;\n"
         "  localparam real R = 1.5;\n"
         "  localparam int NEG = -1;\n"
         "  typedef enum {E0, E1, E2} e_t;\n"
         "  specparam SP = 2;\n"
         "  function automatic int f(int x); return x + 1; endfunction\n"
         "  " +
         items + "\nendmodule\n";
}

std::string Placed(std::string src, const std::string& form) {
  for (std::size_t at = src.find("@@"); at != std::string::npos;
       at = src.find("@@", at + form.size())) {
    src.replace(at, 2, form);
  }
  return src;
}

void ExpectDelayAccepted(const std::string& marked, const std::string& form) {
  const std::string kSrc = Placed(marked, form);
  ElabFixture f;
  auto* design = Elaborate(kSrc, f);
  ASSERT_NE(design, nullptr) << kSrc;
  EXPECT_FALSE(f.has_errors) << kSrc;
}

void ExpectDelayReported(const std::string& marked, const std::string& form,
                         const char* message) {
  const std::string kSrc = Placed(marked, form);
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(marked, "@@"), "16.7"))
      << kSrc;
}

const char* const kDelayPlaces[] = {
    "assert property (@(posedge clk) @@);",
    "sequence sd; @(posedge clk) @@; endsequence\n  cover property (sd);",
    "property pd; @(posedge clk) @@; endproperty\n  assert property (pd);",
};

TEST(CycleDelayConstant, EveryConstantIntegerDelayIsAccepted) {
  for (const char* place : kDelayPlaces) {
    for (const char* form :
         {"a ##7 b", "a ##P b", "a ##(P) b", "##P b", "a ##[1:P] b", "a ##E2 b",
          "a ##SP b", "a ##($clog2(8)) b", "a ##[1:$clog2(8)] b",
          "a ##(f(1)) b", "a ##(int'(2.5)) b"}) {
      ExpectDelayAccepted(DelayBench(place), form);
    }
  }
}

TEST(CycleDelayConstant, AGenvarDelayIsAccepted) {
  ExpectDelayAccepted(
      DelayBench("for (genvar g = 1; g < 3; g++) begin : lg\n"
                 "    assert property (@(posedge clk) a ##g b);\n  end"),
      "");
}

TEST(CycleDelayConstant, DISABLED_EveryNonIntegerDelayIsReported) {
  for (const char* place : kDelayPlaces) {
    for (const char* form : {"a ##2.5 b", "a ##\"two\" b", "a ##R b",
                             "a ##(2.5) b", "a ##(R) b"}) {
      ExpectDelayReported(DelayBench(place), form, kNotInteger);
    }
  }
}

TEST(CycleDelayConstant, DISABLED_EveryNonConstantDelayIsReported) {
  for (const char* place : kDelayPlaces) {
    for (const char* form :
         {"a ##n b", "a ##(n) b", "##n b", "a ##[1:n] b", "a ##[n:3] b",
          "a ##[n:$] b", "a ##C b", "a ##($urandom) b"}) {
      ExpectDelayReported(DelayBench(place), form, kNotConstant);
    }
  }
}

std::string DelayUnit(const char* kind, const char* sequence = "a ##2 b") {
  const bool kChecker = std::string(kind) == "checker";
  return std::string(kind) + " u_unit" +
         (kChecker ? "(logic clk)" : "(input logic clk)") +
         ";\n"
         "  logic a = 1, b = 1;\n"
         "  int n;\n" +
         (kChecker ? ""
                   : "  localparam int P = 2;\n"
                     "  localparam real R = 1.5;\n"
                     "  localparam int NEG = -1;\n") +
         "  sequence su; @(posedge clk) " + sequence +
         "; endsequence\n"
         "  cover property (su);\n"
         "  assert property (@(posedge clk) @@);\n"
         "end" +
         kind + "\n";
}

const char kDelayPackage[] =
    "package pk;\n"
    "  logic pclk = 0, pa = 1;\n"
    "  int pn;\n"
    "  localparam int PP = 2;\n"
    "  localparam real PR = 1.5;\n"
    "  sequence ps; @(posedge pclk) @@; endsequence\n"
    "endpackage\n";

const char kDelayUnitScope[] =
    "logic uclk = 0, ua = 1;\n"
    "int un;\n"
    "localparam int UP = 2;\n"
    "localparam real UR = 1.5;\n"
    "sequence us; @(posedge uclk) @@; endsequence\n";

const char kDelayGenerate[] =
    "if (1) begin : g assert property (@(posedge clk) @@); end";

TEST(CycleDelayConstant, EveryUnitAcceptsAConstantIntegerDelay) {
  for (const char* kind : {"interface", "program"}) {
    ExpectDelayAccepted(DelayBench("u_unit u(clk);", DelayUnit(kind)),
                        "a ##P b");
  }
  ExpectDelayAccepted(DelayBench("u_unit u(clk);", DelayUnit("checker")),
                      "a ##2 b");
  ExpectDelayAccepted(DelayBench("cover property (pk::ps);", kDelayPackage),
                      "pa ##PP pa");
  ExpectDelayAccepted(DelayBench("cover property (us);", kDelayUnitScope),
                      "ua ##UP ua");
  ExpectDelayAccepted(DelayBench(kDelayGenerate), "a ##P b");
}

TEST(CycleDelayConstant, DISABLED_EveryUnitReportsAVariableOrRealDelay) {
  for (const char* kind : {"interface", "program"}) {
    const std::string kMarked = DelayBench("u_unit u(clk);", DelayUnit(kind));
    ExpectDelayReported(kMarked, "a ##n b", kNotConstant);
    ExpectDelayReported(kMarked, "a ##R b", kNotInteger);
  }
  const std::string kChecker =
      DelayBench("u_unit u(clk);", DelayUnit("checker"));
  ExpectDelayReported(kChecker, "a ##n b", kNotConstant);
  ExpectDelayReported(kChecker, "a ##2.5 b", kNotInteger);
  const std::string kPackage =
      DelayBench("cover property (pk::ps);", kDelayPackage);
  ExpectDelayReported(kPackage, "pa ##pn pa", kNotConstant);
  ExpectDelayReported(kPackage, "pa ##PR pa", kNotInteger);
  const std::string kUnit = DelayBench("cover property (us);", kDelayUnitScope);
  ExpectDelayReported(kUnit, "ua ##un ua", kNotConstant);
  ExpectDelayReported(kUnit, "ua ##UR ua", kNotInteger);
  ExpectDelayReported(DelayBench(kDelayGenerate), "a ##n b", kNotConstant);
  ExpectDelayReported(DelayBench(kDelayGenerate), "a ##R b", kNotInteger);
}

bool NegativeReported(const std::vector<Diagnostic>& diags, uint32_t line) {
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError && diag.loc.line == line &&
        diag.subclause == "16.7" &&
        (diag.message.find("0 or greater") != std::string::npos ||
         diag.message.find("cannot be negative") != std::string::npos)) {
      return true;
    }
  }
  return false;
}

void ExpectNegativeReported(const std::string& marked, const std::string& form,
                            std::string_view at = "@@") {
  const std::string kSrc = Placed(marked, form);
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(kSrc, f);
  EXPECT_TRUE(NegativeReported(f.diag.Diagnostics(), LineHolding(marked, at)))
      << kSrc;
}

const char* const kNegativePlaces[] = {
    "assert property (@(posedge clk) @@);",
    "sequence sd; @(posedge clk) @@; endsequence\n  cover property (sd);",
    "property pd; @(posedge clk) @@; endproperty\n  assert property (pd);",
    "assume property (@(posedge clk) @@);",
    "cover property (@(posedge clk) @@);",
    "always @(posedge clk) assert property (@@);",
};

TEST(CycleDelayNonNegative, EveryPlaceAcceptsAZeroOrPositiveDelay) {
  for (const char* place : kNegativePlaces) {
    for (const char* form :
         {"a ##[1:5] b", "a ##[0:$] b", "a ##(1) b", "a ##0 b", "##0 b"}) {
      ExpectDelayAccepted(DelayBench(place), form);
    }
  }
}

TEST(CycleDelayNonNegative, EveryPlaceReportsANegativeParameterOrFoldedDelay) {
  for (const char* place : kNegativePlaces) {
    for (const char* form :
         {"a ##NEG b", "a ##(NEG) b", "a ##(0-1) b", "a ##[NEG:2] b",
          "a ##[0:NEG] b", "a ##[NEG:$] b", "a ##[(0-1):2] b", "##NEG b",
          "a ##['sd0-1:2] b"}) {
      ExpectNegativeReported(DelayBench(place), form);
    }
  }
}

TEST(CycleDelayNonNegative, DISABLED_EveryPlaceReportsANegativeLiteralDelay) {
  for (const char* place : kNegativePlaces) {
    for (const char* form :
         {"a ##[-1:5] b", "a ##[1:-1] b", "a ##[-1:$] b", "a ##(-1) b",
          "a ##(-3) b", "a ##[(-2):3] b", "a ##[0:(-1)] b", "a ##[-(1):2] b",
          "##[-1:2] b", "##(-1) b"}) {
      ExpectNegativeReported(DelayBench(place), form);
    }
  }
}

const char kFormalDelay[] =
    "sequence sf(d); @(posedge clk) a ##d b; endsequence\n"
    "  cover property (sf(@@));";

TEST(CycleDelayNonNegative, APositiveActualIsAccepted) {
  ExpectDelayAccepted(DelayBench(kFormalDelay), "3");
}

const char kCheckerDelay[] =
    "checker ckd(logic clk, int n);\n"
    "  assert property (@(posedge clk) 1 ##n 1);\n"
    "endchecker\n";

TEST(CycleDelayNonNegative, ACheckerFormalDelayIsChecked) {
  ExpectNegativeReported(DelayBench("ckd k(clk, @@);", kCheckerDelay), "-1",
                         "1 ##n 1");
  ExpectDelayAccepted(DelayBench("ckd k(clk, @@);", kCheckerDelay), "2");
}

const char kNegativePackage[] =
    "package pk;\n"
    "  logic pclk = 0, pa = 1;\n"
    "  localparam int PNEG = -1;\n"
    "  sequence ps; @(posedge pclk) @@; endsequence\n"
    "endpackage\n";

const char kNegativeUnitScope[] =
    "logic uclk = 0, ua = 1;\n"
    "localparam int UNEG = -1;\n"
    "sequence us; @(posedge uclk) @@; endsequence\n";

const char kNegativeGenerate[] =
    "if (1) begin : g\n"
    "    sequence gs; @(posedge clk) @@; endsequence\n"
    "    cover property (gs);\n"
    "  end";

TEST(CycleDelayNonNegative, EveryUnitAcceptsAZeroOrPositiveDelay) {
  for (const char* kind : {"interface", "program"}) {
    ExpectDelayAccepted(DelayBench("u_unit u(clk);", DelayUnit(kind)),
                        "a ##[0:5] b");
  }
  ExpectDelayAccepted(DelayBench("u_unit u(clk);", DelayUnit("checker")),
                      "a ##(1) b");
  ExpectDelayAccepted(DelayBench("cover property (pk::ps);", kNegativePackage),
                      "pa ##[0:2] pa");
  ExpectDelayAccepted(DelayBench("cover property (us);", kNegativeUnitScope),
                      "ua ##[0:2] ua");
  ExpectDelayAccepted(DelayBench(kNegativeGenerate), "a ##[0:2] b");
}

TEST(CycleDelayNonNegative, ASequenceDeclarationReportsANegativeLiteralRange) {
  for (const char* form : {"a ##[-1:5] b", "a ##[1:-1] b", "##[-1:2] b"}) {
    ExpectNegativeReported(DelayBench(kNegativePlaces[1]), form);
  }
  for (const char* kind : {"interface", "program", "checker"}) {
    ExpectNegativeReported(DelayBench("u_unit u(clk);", DelayUnit(kind, "@@")),
                           "a ##[-1:5] b");
  }
  ExpectNegativeReported(
      DelayBench("cover property (pk::ps);", kNegativePackage),
      "pa ##[-1:2] pa");
  ExpectNegativeReported(DelayBench("cover property (us);", kNegativeUnitScope),
                         "ua ##[-1:2] ua");
  ExpectNegativeReported(DelayBench(kNegativeGenerate), "a ##[-1:2] b");
}

TEST(CycleDelayNonNegative, AnInterfaceOrProgramReportsANegativeParameter) {
  for (const char* kind : {"interface", "program"}) {
    ExpectNegativeReported(DelayBench("u_unit u(clk);", DelayUnit(kind)),
                           "a ##NEG b");
  }
}

TEST(CycleDelayNonNegative, DISABLED_EveryUnitReportsANegativeDelay) {
  for (const char* kind : {"interface", "program", "checker"}) {
    for (const char* form : {"a ##[-1:5] b", "a ##(-1) b"}) {
      ExpectNegativeReported(DelayBench("u_unit u(clk);", DelayUnit(kind)),
                             form);
    }
  }
  const std::string kPackage =
      DelayBench("cover property (pk::ps);", kNegativePackage);
  const std::string kUnit =
      DelayBench("cover property (us);", kNegativeUnitScope);
  const std::string kGenerate = DelayBench(kNegativeGenerate);
  ExpectNegativeReported(kPackage, "pa ##PNEG pa");
  ExpectNegativeReported(kUnit, "ua ##UNEG ua");
  ExpectNegativeReported(kGenerate, "a ##NEG b");
  ExpectNegativeReported(DelayBench(kDelayGenerate), "a ##NEG b");
}

int InvertedReports(const std::vector<Diagnostic>& diags, uint32_t line) {
  int count = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError && diag.loc.line == line &&
        diag.subclause == "16.7" &&
        (diag.message.find("at least the lower") != std::string::npos ||
         diag.message.find("no less than its minimum") != std::string::npos)) {
      ++count;
    }
  }
  return count;
}

void ExpectInvertedOnce(const std::string& marked, const std::string& form,
                        std::string_view at = "@@") {
  const std::string kSrc = Placed(marked, form);
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(kSrc, f);
  EXPECT_EQ(InvertedReports(f.diag.Diagnostics(), LineHolding(marked, at)), 1)
      << kSrc;
}

const char* const kRangePlaces[] = {
    "assert property (@(posedge clk) @@);",
    "sequence sd; @(posedge clk) @@; endsequence\n  cover property (sd);",
    "property pd; @(posedge clk) @@; endproperty\n  assert property (pd);",
    "assume property (@(posedge clk) @@);",
    "cover property (@(posedge clk) @@);",
    "restrict property (@(posedge clk) @@);",
    "always @(posedge clk) assert property (@@);",
    "initial expect (@(posedge clk) @@);",
};

TEST(CycleDelayRangeOrder, EveryPlaceAcceptsAnOrderedRange) {
  for (const char* place : kRangePlaces) {
    for (const char* form :
         {"a ##[1:5] b", "a ##[3:3] b", "a ##[3:$] b", "a ##[*] b", "a ##[+] b",
          "a ##[(1):(5)] b", "a ##[8'h1:8'h5] b", "a ##[2:1_0] b", "##[2:4] b",
          "a ##[P:P+2] b"}) {
      ExpectDelayAccepted(DelayBench(place), form);
    }
  }
}

TEST(CycleDelayRangeOrder, EveryPlaceReportsAnInvertedParameterRange) {
  for (const char* place : kRangePlaces) {
    for (const char* form : {"a ##[P+2:P] b", "a ##[P:1] b"}) {
      ExpectInvertedOnce(DelayBench(place), form);
    }
  }
}

TEST(CycleDelayRangeOrder, DISABLED_EveryPlaceReportsAnInvertedLiteralRange) {
  for (const char* place : kRangePlaces) {
    for (const char* form :
         {"a ##[5:1] b", "##[4:2] b", "a ##[(5):(1)] b", "a ##[8'h5:8'h1] b",
          "a ##[3'd5:3'd1] b", "a ##[1_0:2] b"}) {
      ExpectInvertedOnce(DelayBench(place), form);
    }
  }
}

TEST(CycleDelayRangeOrder, ASequenceDeclarationReportsAPlainLiteralRange) {
  ExpectInvertedOnce(DelayBench(kRangePlaces[1]), "a ##[5:1] b");
  ExpectInvertedOnce(DelayBench(kRangePlaces[1]), "##[4:2] b");
}

const char* const kImplicationPlaces[] = {
    "assert property (@(posedge clk) @@);",
    "property pd; @(posedge clk) @@; endproperty\n  assert property (pd);",
};

TEST(CycleDelayRangeOrder, AConsequentsOrderedRangeIsAccepted) {
  for (const char* place : kImplicationPlaces) {
    ExpectDelayAccepted(DelayBench(place), "a |-> ##[2:4] b");
  }
}

TEST(CycleDelayRangeOrder, DISABLED_AConsequentsInvertedRangeIsReported) {
  for (const char* place : kImplicationPlaces) {
    ExpectInvertedOnce(DelayBench(place), "a |-> ##[4:2] b");
  }
}

TEST(CycleDelayRangeOrder, EveryUnitsSequenceDeclarationReportsAnInversion) {
  for (const char* kind : {"interface", "program", "checker"}) {
    ExpectDelayAccepted(DelayBench("u_unit u(clk);", DelayUnit(kind, "@@")),
                        "a ##[1:5] b");
    ExpectInvertedOnce(DelayBench("u_unit u(clk);", DelayUnit(kind, "@@")),
                       "a ##[5:1] b");
  }
  ExpectInvertedOnce(DelayBench("cover property (pk::ps);", kNegativePackage),
                     "pa ##[5:1] pa");
  ExpectInvertedOnce(DelayBench("cover property (us);", kNegativeUnitScope),
                     "ua ##[5:1] ua");
  ExpectInvertedOnce(DelayBench(kNegativeGenerate), "a ##[5:1] b");
}

TEST(CycleDelayRangeOrder, DISABLED_AUnitsAssertionOrGenerateParameterInverts) {
  for (const char* kind : {"interface", "program", "checker"}) {
    ExpectInvertedOnce(DelayBench("u_unit u(clk);", DelayUnit(kind)),
                       "a ##[5:1] b");
  }
  ExpectInvertedOnce(DelayBench(kDelayGenerate), "a ##[5:1] b");
  ExpectInvertedOnce(DelayBench(kNegativeGenerate), "a ##[P:1] b");
}

TEST(CycleDelayRangeOrder, AnInterfaceOrProgramReportsAnInvertedParameter) {
  for (const char* kind : {"interface", "program"}) {
    ExpectDelayAccepted(DelayBench("u_unit u(clk);", DelayUnit(kind)),
                        "a ##[1:P] b");
    ExpectInvertedOnce(DelayBench("u_unit u(clk);", DelayUnit(kind)),
                       "a ##[P:1] b");
  }
}

const char kSequenceFormal[] =
    "sequence sf(int d); @(posedge clk) a ##[5:d] b; endsequence\n"
    "  cover property (sf(@@));";

TEST(CycleDelayRangeOrder, ASequenceFormalIsCheckedPerInstance) {
  ExpectInvertedOnce(DelayBench(kSequenceFormal), "2", "##[5:d]");
  ExpectDelayAccepted(DelayBench(kSequenceFormal), "9");
}

const char kPropertyFormal[] =
    "property qf(int d); @(posedge clk) a ##[d:1] b; endproperty\n"
    "  assert property (qf(@@));";

TEST(CycleDelayRangeOrder, APropertyFormalWithAnOrderedActualIsAccepted) {
  ExpectDelayAccepted(DelayBench(kPropertyFormal), "0");
}

TEST(CycleDelayRangeOrder, DISABLED_APropertyFormalIsCheckedPerInstance) {
  ExpectInvertedOnce(DelayBench(kPropertyFormal), "3", "##[d:1]");
}

const char kDefaultedFormal[] =
    "sequence tf(int d = 1); @(posedge clk) a ##[5:d] b; endsequence\n"
    "  @@";

TEST(CycleDelayRangeOrder, AnUninstancedDefaultIsNotChecked) {
  ExpectDelayAccepted(DelayBench(kDefaultedFormal), "");
}

TEST(CycleDelayRangeOrder, DISABLED_ADefaultIsCheckedOnlyWhereItIsUsed) {
  ExpectDelayAccepted(DelayBench(kDefaultedFormal), "cover property (tf(9));");
  ExpectInvertedOnce(DelayBench(kDefaultedFormal), "cover property (tf(2));",
                     "##[5:d]");
  ExpectInvertedOnce(DelayBench(kDefaultedFormal), "cover property (tf());",
                     "##[5:d]");
}

}  // namespace
