#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// 18.5.3 / Syntax 18-3: expression_or_dist allows an expression paired with a
// dist set ("expression dist { dist_list }"). A dist_list of weighted single
// values parses as a valid constraint expression.
TEST(ConstraintDistParsing, WeightedValueListAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:=1, 200:=2, 300:=5}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.3: dist_weight may use either the := or the :/ operator on an item.
TEST(ConstraintDistParsing, DivideWeightOperatorAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:/1, 200:/2, 300:/5}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.3: a dist_item may be a value_range with an optional dist_weight.
TEST(ConstraintDistParsing, ValueRangeItemAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:102]:=1, 103:=1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.3: a dist_item may be "default :/ expression"; a default using the :/
// operator is accepted.
TEST(ConstraintDistParsing, DefaultWithDivideWeightAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:102]:/3, default:/1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.3: a distribution's default specification takes the :/ operator only, so
// writing := there is an error.
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

// 18.5.3: a default specification written without its :/ operator is an error.
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

// 18.5.3: a distribution may hold one default specification, never two.
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
