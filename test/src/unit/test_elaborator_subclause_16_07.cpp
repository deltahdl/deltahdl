#include <gtest/gtest.h>

#include <cstddef>
#include <string>

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
  Elaborate(kSrc, f);
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

std::string DelayUnit(const char* kind) {
  const bool kChecker = std::string(kind) == "checker";
  return std::string(kind) + " u_unit" +
         (kChecker ? "(logic clk)" : "(input logic clk)") +
         ";\n"
         "  logic a = 1, b = 1;\n"
         "  int n;\n" +
         (kChecker ? ""
                   : "  localparam int P = 2;\n"
                     "  localparam real R = 1.5;\n") +
         "  sequence su; @(posedge clk) a ##2 b; endsequence\n"
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

}  // namespace
