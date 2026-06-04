#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.12.16 (Syntax 16-17): the `case` form of property_expr —
// `case ( expression_or_dist ) property_case_item { property_case_item }
// endcase` — is accepted in a named property body. This mirrors the LRM
// decoding example with several items and a trailing default.
TEST(PropertyCaseParsing, CaseWithItemsAndDefaultParses) {
  auto r = Parse(
      "module m;\n"
      "  property p_delay(logic [1:0] delay);\n"
      "    case (delay)\n"
      "      2'd0    : a;\n"
      "      2'd1    : a ##2 b;\n"
      "      2'd2    : a ##4 b;\n"
      "      2'd3    : a ##8 b;\n"
      "      default : 1'b0;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

// §16.12.16: the default statement shall be optional — a property case with no
// default item is legal and parses cleanly.
TEST(PropertyCaseParsing, CaseWithoutDefaultParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic [1:0] sel);\n"
      "    case (sel)\n"
      "      2'd0 : a;\n"
      "      2'd1 : b;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.12.16 (property_case_item): an item may list several expression_or_dist
// values separated by commas before the colon, all sharing one property_expr.
TEST(PropertyCaseParsing, CaseItemWithCommaSeparatedExpressionListParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic [1:0] sel);\n"
      "    case (sel)\n"
      "      2'd0, 2'd1, 2'd2 : a;\n"
      "      default          : b;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.12.16 (property_case_item): the colon after `default` is optional in the
// grammar (`default [ : ] property_expr ;`), so omitting it still parses.
TEST(PropertyCaseParsing, DefaultWithoutColonParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic [1:0] sel);\n"
      "    case (sel)\n"
      "      2'd0    : a;\n"
      "      default   b;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.12.16: use of multiple default statements in one property case statement
// shall be illegal.
TEST(PropertyCaseParsing, MultipleDefaultsIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic [1:0] sel);\n"
      "    case (sel)\n"
      "      2'd0    : a;\n"
      "      default : b;\n"
      "      default : c;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.16: the at-most-one-default rule is per case statement. Two sibling
// case property statements, each with its own single default, are legal — the
// defaults are not pooled across the separate `case`..`endcase` regions.
TEST(PropertyCaseParsing, DefaultsInSeparateCasesAreLegal) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic [1:0] sel);\n"
      "    case (sel)\n"
      "      2'd0    : a;\n"
      "      default : b;\n"
      "    endcase\n"
      "    and\n"
      "    case (sel)\n"
      "      2'd1    : c;\n"
      "      default : d;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.12.16: the at-most-one-default rule scopes to a single case statement, so
// a case property nested inside another case item may carry its own default
// while the enclosing case also has one. The inner default is charged to the
// inner case, not pooled with the outer, so two single-default case statements
// nested this way remain legal.
TEST(PropertyCaseParsing, NestedCaseDefaultsCountedPerCase) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic [1:0] sel);\n"
      "    case (sel)\n"
      "      2'd0 : case (sel)\n"
      "               2'd1    : a;\n"
      "               default : b;\n"
      "             endcase\n"
      "      default : c;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.12.16 (property_case_item + default optional): a default item is itself a
// valid property_case_item, so a case property whose sole item is the default
// parses cleanly. A single default is legal — the at-most-one-default rule only
// rejects a second one — so this exercises the boundary between "no error" and
// the multiple-default error.
TEST(PropertyCaseParsing, CaseWithOnlyDefaultItemParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic [1:0] sel);\n"
      "    case (sel)\n"
      "      default : a;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
