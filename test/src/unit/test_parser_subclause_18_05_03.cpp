#include <gtest/gtest.h>

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

}  // namespace
