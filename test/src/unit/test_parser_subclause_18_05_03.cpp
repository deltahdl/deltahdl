#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstraintDistParsing, WeightedValueListAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:=1, 200:=2, 300:=5}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistParsing, DivideWeightOperatorAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:/1, 200:/2, 300:/5}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistParsing, ValueRangeItemAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:102]:=1, 103:=1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistParsing, DefaultWithDivideWeightAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:102]:/3, default:/1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistParsing, DefaultWithAssignWeightRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:102]:/3, default:=1}; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a distribution's default specification takes its "
                            "weight through :/ and nothing else",
                            3, "18.5.3"));
}

TEST(ConstraintDistParsing, DefaultWithoutWeightOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:=1, default 5}; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a distribution's default specification takes its "
                            "weight through :/ and nothing else",
                            3, "18.5.3"));
}

TEST(ConstraintDistParsing, MultipleDefaultsRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {default:/1, default:/2}; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "this distribution already has a default "
                            "specification; it can have only one",
                            3, "18.5.3"));
}

const char* const kDefaultWeight =
    "a distribution's default specification takes its weight through :/ and "
    "nothing else";
const char* const kTwoDefaults =
    "this distribution already has a default specification; it can have only "
    "one";

std::string ExternalDist(const std::string& set) {
  return "class C;\n"
         "  rand int x;\n"
         "  constraint c;\n"
         "endclass\n"
         "constraint C::c { x dist {" +
         set + "}; }\n";
}

std::string InlineDist(const std::string& set) {
  return "module m;\n"
         "  class C;\n"
         "    rand int x;\n"
         "  endclass\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    void'(o.randomize() with { x dist {" +
         set +
         "}; });\n"
         "  end\n"
         "endmodule\n";
}

std::string ScopeDist(const std::string& set) {
  return "module m;\n"
         "  int x;\n"
         "  initial begin\n"
         "    void'(std::randomize(x) with { x dist {" +
         set +
         "}; });\n"
         "  end\n"
         "endmodule\n";
}

void ExpectDefaultReports(std::string (*wrap)(const std::string&), int line) {
  auto assign = Parse(wrap("1 := 1, default := 1"));
  EXPECT_TRUE(ReportedError(assign.diags, kDefaultWeight, line, "18.5.3"));
  auto twice = Parse(wrap("default :/ 1, default :/ 2"));
  EXPECT_TRUE(ReportedError(twice.diags, kTwoDefaults, line, "18.5.3"));
  auto one = Parse(wrap("1 := 1, default :/ 1"));
  EXPECT_FALSE(one.has_errors);
}

TEST(ConstraintDistParsing, DefaultErrorsInAnExternalBlock) {
  ExpectDefaultReports(ExternalDist, 5);
}

TEST(ConstraintDistParsing, DefaultErrorsInAnInlineBlock) {
  ExpectDefaultReports(InlineDist, 7);
}

TEST(ConstraintDistParsing, DefaultErrorsInAScopeRandomizeBlock) {
  ExpectDefaultReports(ScopeDist, 4);
}

TEST(ConstraintDistParsing, DISABLED_ADefaultWithNothingAfterItIsReportedOnce) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:=1, default}; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, kDefaultWeight, 3, "18.5.3"));
  EXPECT_EQ(r.diags.size(), 1u);
}

}  // namespace
