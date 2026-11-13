#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_property_spec_places.h"
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

constexpr const char* kTwoDefaults =
    "property case statement shall have at most one 'default' item";

constexpr const char* kTwoDefaultCases[] = {
    "case (a) 1'b0: b; default: b; default: c; endcase",
    "case (a) 1'b0: b; default b; default c; endcase",
    "case (a) default: b; 1'b0: b; default: c; endcase",
    ("case (a) 1'b0: case (b) default: c; default c; endcase; default: c; "
     "endcase")};

constexpr const char* kOneDefaultOrNoneCases[] = {
    "case (a) 1'b0: b; default: c; endcase",
    "case (a) 1'b0: b; default c; endcase",
    "case (a) 1'b0: b; 1'b1: c; endcase",
    "case (a) 1'b0: case (b) default: c; endcase; default: c; endcase"};

constexpr const char* kDeclarationPlaces[] = {
    "module",  "package",  "interface", "program",
    "checker", "generate", "clocking",  "unit"};

std::string DeclaredCaseIn(const std::string& place, const std::string& spec) {
  const std::string kSignals = "  logic clk; bit a, b, c;\n";
  const std::string kDeclared = "property q; " + spec + "; endproperty";
  if (place == "unit") return "\n" + kSignals + "  " + kDeclared + "\n";
  std::string unit =
      place == "generate" || place == "clocking" ? "module" : place;
  std::string line = "  " + kDeclared;
  if (place == "generate") line = "  if (1) begin : g " + kDeclared + " end";
  if (place == "clocking") {
    line = "  clocking cb @(posedge clk); " + kDeclared + " endclocking";
  }
  return unit + " m;\n" + kSignals + line + "\nend" + unit + "\n";
}

constexpr const char* kStatementPlaces[] = {
    "module",  "assume",     "cover",         "restrict",  "expect",
    "nested",  "procedural", "generate",      "interface", "program",
    "checker", "actual",     "formal default"};

std::string StatedCaseIn(const std::string& place, const std::string& spec) {
  const std::string kSignals =
      "  logic clk; bit a, b, c; property p(property r); r; endproperty\n";
  std::string clocked = "@(posedge clk) " + spec;
  std::string line = "  assert property (" + clocked + ");";
  if (place == "assume" || place == "cover") {
    line = "  " + place + " property (" + clocked + ");";
  }
  if (place == "restrict") line = "  restrict property (" + clocked + ");";
  if (place == "expect") line = "  initial expect (" + clocked + ");";
  if (place == "nested") {
    line = "  assert property (@(posedge clk) case (c) 1'b1: " + spec +
           "; default: a; endcase);";
  }
  if (place == "procedural") {
    line = "  always @(posedge clk) assert property (" + spec + ");";
  }
  if (place == "generate") line = "  if (1) begin : g" + line + " end";
  if (place == "actual") {
    line = "  assert property (@(posedge clk) p(" + spec + "));";
  }
  if (place == "formal default") {
    line = "  property f(property r = " + spec + "); r; endproperty";
  }
  std::string unit =
      place == "interface" || place == "program" || place == "checker"
          ? place
          : "module";
  return unit + " m;\n" + kSignals + line + "\nend" + unit + "\n";
}

TEST(PropertyCaseParsing, TwoDefaultsInANamedPropertyAreReportedInEachPlace) {
  for (const char* place : kDeclarationPlaces) {
    for (const char* spec : kTwoDefaultCases) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(DeclaredCaseIn(place, spec));
      EXPECT_TRUE(ReportedError(r.diags, kTwoDefaults, 3, "16.12.16"));
    }
  }
}

TEST(PropertyCaseParsing,
     OneDefaultOrNoneInANamedPropertyIsAcceptedInEachPlace) {
  for (const char* place : kDeclarationPlaces) {
    for (const char* spec : kOneDefaultOrNoneCases) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(DeclaredCaseIn(place, spec));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

TEST(PropertyCaseParsing,
     DISABLED_TwoDefaultsOutsideANamedPropertyBodyAreReportedInEachPlace) {
  for (const char* place : kStatementPlaces) {
    for (const char* spec : kTwoDefaultCases) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(StatedCaseIn(place, spec));
      EXPECT_TRUE(ReportedError(r.diags, kTwoDefaults, 3, "16.12.16"));
    }
  }
}

TEST(PropertyCaseParsing,
     OneDefaultOrNoneOutsideANamedPropertyBodyIsAcceptedInEachPlace) {
  for (const char* place : kStatementPlaces) {
    for (const char* spec : kOneDefaultOrNoneCases) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(StatedCaseIn(place, spec));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

TEST(PropertyCaseParsing, ACaseIsAcceptedInEachPropertySpecPlace) {
  for (const char* place : kPropertySpecPlaces) {
    for (const char* spec : kOneDefaultOrNoneCases) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(PropertySpecIn(place, spec));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

TEST(PropertyCaseParsing, ADistributionIsAcceptedAsTheCaseOrAnItemExpression) {
  for (const char* place : kPropertySpecPlaces) {
    for (const char* spec :
         {"case (a dist {0 := 1, 1 := 3}) 1'b0: b; default: c; endcase",
          "case (a) b dist {0 :/ 1, 1 :/ 2}, c: b; default: c; endcase"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(PropertySpecIn(place, spec));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

}  // namespace
