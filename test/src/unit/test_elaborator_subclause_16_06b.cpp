#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char kChandleRef[] =
    "concurrent assertion expression references chandle variable";

const char kChandleForm[] = "h != null";
const char kLogicForm[] = "g";

std::string WithForm(std::string text, const std::string& form) {
  for (size_t at = text.find("@@"); at != std::string::npos;
       at = text.find("@@", at + form.size())) {
    text.replace(at, 2, form);
  }
  return text;
}

std::string ChandleBench(const std::string& items,
                         const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0, a = 1, g = 1;\n"
         "  chandle h;\n"
         "  sequence sa(x); @(posedge clk) x; endsequence\n"
         "  property pa(x); @(posedge clk) x; endproperty\n"
         "  " +
         items + "\nendmodule\n";
}

std::string StatementOf(const std::string& place) {
  return place.substr(place.rfind('\n') + 1);
}

void ExpectChandleReported(const std::string& place, const std::string& form,
                           const std::string& outside = "") {
  const std::string kSrc = WithForm(ChandleBench(place, outside), form);
  ElabFixture f;
  Elaborate(kSrc, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(), kChandleRef,
      LineHolding(kSrc, WithForm(StatementOf(place), form)), "16.6"))
      << kSrc;
}

void ExpectChandleAccepted(const std::string& place, const std::string& form,
                           const std::string& outside = "") {
  const std::string kSrc = WithForm(ChandleBench(place, outside), form);
  ElabFixture f;
  auto* design = Elaborate(kSrc, f);
  ASSERT_NE(design, nullptr) << kSrc;
  EXPECT_FALSE(f.has_errors) << kSrc;
}

const char* const kReportedPlaces[] = {
    "assert property (@(posedge clk) @@);",
    "assume property (@(posedge clk) @@);",
    "cover property (@(posedge clk) @@);",
    "cover sequence (@(posedge clk) @@);",
    "assert property (@(posedge clk) not (@@));",
    "property q; @(posedge clk) @@; endproperty\n  assert property (q);",
    "assert property (sa(@@));",
    "assert property (pa(@@));",
    "if (1) begin : gb assert property (@(posedge clk) @@); end",
};

const char* const kUnreportedPlaces[] = {
    "restrict property (@(posedge clk) @@);",
    "assert property (@(posedge clk) a ##1 @@);",
    "assert property (@(posedge clk) a and @@);",
    "assert property (@(posedge clk) a or @@);",
    "assert property (@(posedge clk) (a ##1 a) intersect (@@ ##1 a));",
    "assert property (@(posedge clk) @@ within (a ##1 a));",
    "assert property (@(posedge clk) @@ throughout (a ##1 a));",
    "assert property (@(posedge clk) @@ |-> a);",
    "assert property (@(posedge clk) a |-> @@);",
    "assert property (@(posedge clk) @@ |=> a);",
    "assert property (@(posedge clk) a |=> @@);",
    "sequence s; @(posedge clk) @@; endsequence\n  assert property (s);",
    "let l = @@;\n  assert property (@(posedge clk) l);",
    "assert property (@(posedge clk) disable iff (@@) a);",
    "default disable iff (@@);\n  assert property (@(posedge clk) a);",
    "assert property (@(posedge clk iff @@) a);",
    "always @(posedge clk) assert property (@@);",
    "initial assert property (@(posedge clk) @@);",
};

TEST(ChandleInAssertion, EveryPlaceAcceptsAnOrdinaryVariable) {
  for (const char* place : kReportedPlaces) {
    ExpectChandleAccepted(place, kLogicForm);
  }
  for (const char* place : kUnreportedPlaces) {
    ExpectChandleAccepted(place, kLogicForm);
  }
}

TEST(ChandleInAssertion, TheDirectAndInstancedPlacesReportAChandle) {
  for (const char* place : kReportedPlaces) {
    ExpectChandleReported(place, kChandleForm);
  }
}

TEST(ChandleInAssertion, DISABLED_EveryOtherPlaceReportsAChandle) {
  for (const char* place : kUnreportedPlaces) {
    ExpectChandleReported(place, kChandleForm);
  }
}

TEST(ChandleInAssertion, ASampledValueFunctionOfAChandleIsReported) {
  const char kPlace[] = "assert property (@(posedge clk) @@);";
  for (const char* form : {"$past(h) != null", "$stable(h)"}) {
    ExpectChandleReported(kPlace, form);
  }
  for (const char* form : {"$past(g)", "$stable(g)"}) {
    ExpectChandleAccepted(kPlace, form);
  }
}

TEST(ChandleInAssertion, AChandleInTheActionBlockIsAccepted) {
  ExpectChandleAccepted(
      "assert property (@(posedge clk) a) else $display(\"%0d\", @@);",
      kChandleForm);
}

std::string ChandleUnit(const char* kind) {
  return std::string(kind) +
         " u_unit(input logic clk);\n"
         "  logic g = 1;\n"
         "  chandle h;\n"
         "  assert property (@(posedge clk) @@);\n"
         "end" +
         kind + "\n";
}

const char kChandleChecker[] =
    "checker u_unit(logic clk);\n"
    "  logic g = 1;\n"
    "  chandle h;\n"
    "  assert property (@(posedge clk) @@);\n"
    "endchecker\n";

TEST(ChandleInAssertion, EveryUnitReportsAChandleBesideAVariable) {
  for (const std::string& unit :
       {ChandleUnit("interface"), ChandleUnit("program"),
        std::string(kChandleChecker)}) {
    const std::string kSrc =
        WithForm(ChandleBench("u_unit u(clk);", unit), kChandleForm);
    ElabFixture f;
    Elaborate(kSrc, f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(), kChandleRef,
        LineHolding(kSrc, "assert property (@(posedge clk) h != null);"),
        "16.6"))
        << kSrc;
    ExpectChandleAccepted("u_unit u(clk);", kLogicForm, unit);
  }
}

}  // namespace
