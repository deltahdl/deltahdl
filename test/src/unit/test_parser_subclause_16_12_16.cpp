#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

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
  EXPECT_TRUE(ReportedError(
      r.diags, "property case statement shall have at most one 'default' item",
      6, "16.12.16"));
}

TEST(PropertyCaseParsing, MultipleColonlessDefaultsIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic [1:0] sel);\n"
      "    case (sel)\n"
      "      2'd0    : a;\n"
      "      default   b;\n"
      "      default   c;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "property case statement shall have at most one 'default' item",
      6, "16.12.16"));
}

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

TEST(PropertyCaseParsing, NestedCaseDefaultsCountedPerCase) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic [1:0] sel);\n"
      "    case (sel)\n"
      "      2'd0 : case (sel)\n"
      "               2'd1    : a;\n"
      "               default : b;\n"
      "             endcase;\n"
      "      default : c;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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
