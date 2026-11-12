#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(SequenceExpressionParsing, SequenceConcatDelay) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##2 b ##3 c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, RangedRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##[1:5] b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, UnboundedDelayRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[0:$] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, ZeroDelayConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##0 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, UnboundedStarShorthandParses) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[*] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, UnboundedPlusShorthandParses) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[+] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, BooleanAndOrIntersectAlternativesParse) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_and;\n"
      "    @(posedge clk) a and b;\n"
      "  endsequence\n"
      "  sequence s_or;\n"
      "    @(posedge clk) a or b;\n"
      "  endsequence\n"
      "  sequence s_intersect;\n"
      "    @(posedge clk) a intersect b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, FirstMatchAndThroughoutWithinParse) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_fm;\n"
      "    @(posedge clk) first_match(a ##1 b);\n"
      "  endsequence\n"
      "  sequence s_th;\n"
      "    @(posedge clk) a throughout (b ##1 c);\n"
      "  endsequence\n"
      "  sequence s_wi;\n"
      "    @(posedge clk) (a ##1 b) within (c ##1 d ##1 e);\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, ConsecutiveRepetitionAbbreviationsParse) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_count;\n"
      "    @(posedge clk) a[*3];\n"
      "  endsequence\n"
      "  sequence s_star;\n"
      "    @(posedge clk) a[*];\n"
      "  endsequence\n"
      "  sequence s_plus;\n"
      "    @(posedge clk) a[+];\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, GotoAndNonconsecutiveRepetitionParse) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_goto;\n"
      "    @(posedge clk) a[->2] ##1 b;\n"
      "  endsequence\n"
      "  sequence s_nonc;\n"
      "    @(posedge clk) a[=3] ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, SequenceMatchItemListParses) {
  auto r = Parse(
      "module m;\n"
      "  int lv;\n"
      "  sequence s;\n"
      "    @(posedge clk) (a ##1 b, lv = 1, lv++);\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, ParenthesizedSequenceWithAbbrevParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) (a ##1 b)[*2];\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, InvertedDelayRangeIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[5:1] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "cycle-delay range upper bound must be at least the lower bound",
      3, "16.7"));
}

TEST(SequenceExpressionParsing, NegativeDelayRangeBoundIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[-1:5] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "cycle-delay range bounds cannot be negative", 3, "16.7"));
}

TEST(SequenceExpressionParsing, NegativeUpperDelayRangeBoundIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[1:-1] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "cycle-delay range bounds cannot be negative", 3, "16.7"));
}

TEST(SequenceExpressionParsing, EqualDelayRangeBoundsIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[3:3] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, MinTypMaxCycleDelayValueIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(1:2:3) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a min:typ:max expression may not be used as a cycle-delay value", 3,
      "16.7"));
}

TEST(SequenceExpressionParsing, ParenthesizedConditionalCycleDelayIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  parameter SEL = 1;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(SEL ? 1 : 2) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, MinTypMaxCycleDelayWithParamOperandsIsError) {
  auto r = Parse(
      "module m;\n"
      "  parameter MIN_D = 1, TYP_D = 2, MAX_D = 3;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(MIN_D:TYP_D:MAX_D) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a min:typ:max expression may not be used as a cycle-delay value", 4,
      "16.7"));
}

TEST(SequenceExpressionParsing, ParenthesizedParamCycleDelayIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  parameter DLY = 2;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(DLY) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, RealLiteralCycleDelayValueIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##2.5 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "cycle-delay value must be an integer", 3,
                            "16.7"));
}

TEST(SequenceExpressionParsing, StringLiteralCycleDelayValueIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##\"two\" b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "cycle-delay value must be an integer", 3,
                            "16.7"));
}

TEST(SequenceExpressionParsing, IntegerLiteralCycleDelayValueIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##7 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, ExpressionOrDistInsideSequenceParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    @(posedge clk) (a dist {0 := 80, 1 := 20}) |-> b;\n"
      "  endproperty\n"
      "  assert property (p);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

struct CycleDelayPlace {
  const char* name;
  const char* source;
  uint32_t line;
};

constexpr CycleDelayPlace kCycleDelayPlaces[] = {
    {"sequence declaration",
     "module m;\n  logic clk, a, b;\n"
     "  sequence s; @(posedge clk) a FORM b; endsequence\nendmodule\n",
     3},
    {"leading delay of a sequence declaration",
     "module m;\n  logic clk, a, b;\n"
     "  sequence s; @(posedge clk) FORM a; endsequence\nendmodule\n",
     3},
    {"property declaration",
     "module m;\n  logic clk, a, b;\n"
     "  property p; @(posedge clk) a FORM b; endproperty\nendmodule\n",
     3},
    {"module assert property",
     "module m;\n  logic clk, a, b;\n"
     "  assert property (@(posedge clk) a FORM b);\nendmodule\n",
     3},
    {"package sequence declaration",
     "package pk;\n  bit clk, a, b;\n"
     "  sequence s; @(posedge clk) a FORM b; endsequence\nendpackage\n",
     3},
    {"interface assert property",
     "interface i;\n  logic clk, a, b;\n"
     "  assert property (@(posedge clk) a FORM b);\nendinterface\n",
     3},
    {"program assert property",
     "program g;\n  logic clk, a, b;\n"
     "  assert property (@(posedge clk) a FORM b);\nendprogram\n",
     3},
    {"checker assert property",
     "checker c(logic clk, a, b);\n"
     "  assert property (@(posedge clk) a FORM b);\nendchecker\n",
     2},
    {"generate block assert property",
     "module m;\n  logic clk, a, b;\n  if (1) begin : gb\n"
     "    assert property (@(posedge clk) a FORM b);\n  end\nendmodule\n",
     4},
    {"procedural assert property",
     "module m;\n  logic clk, a, b;\n  always @(posedge clk) begin\n"
     "    assert property (a FORM b);\n  end\nendmodule\n",
     4}};

std::string WithCycleDelay(const char* source, const std::string& form) {
  std::string text = source;
  text.replace(text.find("FORM"), 4, form);
  return text;
}

TEST(CycleDelaySyntax, MalformedBracketFormsAreReportedInEveryPlace) {
  const char* const kForms[] = {"##[3]", "##[*3]", "##[+3]", "##[$]"};
  for (const auto& place : kCycleDelayPlaces) {
    for (const char* form : kForms) {
      auto r = Parse(WithCycleDelay(place.source, form));
      EXPECT_TRUE(ReportedError(r.diags, "is not one the grammar admits",
                                place.line, "A.2.10"))
          << place.name << ": " << form;
    }
  }
}

TEST(CycleDelaySyntax, WellFormedBracketFormsParseInEveryPlace) {
  const char* const kForms[] = {"##[3:3]", "##[*]", "##[+]", "##[3:$]",
                                "##[1:3]"};
  for (const auto& place : kCycleDelayPlaces) {
    for (const char* form : kForms) {
      auto r = Parse(WithCycleDelay(place.source, form));
      EXPECT_FALSE(r.has_errors) << place.name << ": " << form;
    }
  }
}

constexpr CycleDelayPlace kMoreCycleDelayPlaces[] = {
    {"leading delay of a property declaration",
     "module m;\n  logic clk, a, b;\n"
     "  property p; @(posedge clk) FORM a; endproperty\nendmodule\n",
     3},
    {"leading delay of an assert property",
     "module m;\n  logic clk, a, b;\n"
     "  assert property (@(posedge clk) FORM a);\nendmodule\n",
     3},
    {"assume property",
     "module m;\n  logic clk, a, b;\n"
     "  assume property (@(posedge clk) a FORM b);\nendmodule\n",
     3},
    {"cover property",
     "module m;\n  logic clk, a, b;\n"
     "  cover property (@(posedge clk) a FORM b);\nendmodule\n",
     3},
    {"cover sequence",
     "module m;\n  logic clk, a, b;\n"
     "  cover sequence (@(posedge clk) a FORM b);\nendmodule\n",
     3},
    {"restrict property",
     "module m;\n  logic clk, a, b;\n"
     "  restrict property (@(posedge clk) a FORM b);\nendmodule\n",
     3},
    {"expect statement",
     "module m;\n  logic clk, a, b;\n"
     "  initial expect (@(posedge clk) a FORM b);\nendmodule\n",
     3},
    {"interface sequence declaration",
     "interface i;\n  logic clk, a, b;\n"
     "  sequence s; @(posedge clk) a FORM b; endsequence\nendinterface\n",
     3},
    {"program sequence declaration",
     "program g;\n  logic clk, a, b;\n"
     "  sequence s; @(posedge clk) a FORM b; endsequence\nendprogram\n",
     3},
    {"checker sequence declaration",
     "checker c(logic clk, a, b);\n"
     "  sequence s; @(posedge clk) a FORM b; endsequence\nendchecker\n",
     2},
    {"generate block sequence declaration",
     "module m;\n  logic clk, a, b;\n  if (1) begin : gb\n"
     "    sequence s; @(posedge clk) a FORM b; endsequence\n  end\n"
     "endmodule\n",
     4},
    {"compilation unit sequence declaration",
     "bit clk, a, b;\n"
     "sequence s; @(posedge clk) a FORM b; endsequence\n",
     2},
    {"interface property declaration",
     "interface i;\n  logic clk, a, b;\n"
     "  property p; @(posedge clk) a FORM b; endproperty\nendinterface\n",
     3},
    {"program property declaration",
     "program g;\n  logic clk, a, b;\n"
     "  property p; @(posedge clk) a FORM b; endproperty\nendprogram\n",
     3},
    {"checker property declaration",
     "checker c(logic clk, a, b);\n"
     "  property p; @(posedge clk) a FORM b; endproperty\nendchecker\n",
     2},
    {"package property declaration",
     "package pk;\n  bit clk, a, b;\n"
     "  property p; @(posedge clk) a FORM b; endproperty\nendpackage\n",
     3},
    {"generate block property declaration",
     "module m;\n  logic clk, a, b;\n  if (1) begin : gb\n"
     "    property p; @(posedge clk) a FORM b; endproperty\n  end\n"
     "endmodule\n",
     4},
    {"compilation unit property declaration",
     "bit clk, a, b;\n"
     "property p; @(posedge clk) a FORM b; endproperty\n",
     2}};

const char kMinTypMax[] =
    "a min:typ:max expression may not be used as a cycle-delay value";

template <typename Places>
void ExpectEveryPlaceAccepts(const Places& places,
                             std::initializer_list<const char*> forms) {
  for (const auto& place : places) {
    for (const char* form : forms) {
      auto r = Parse(WithCycleDelay(place.source, form));
      EXPECT_FALSE(r.has_errors) << place.name << ": " << form;
    }
  }
}

bool InASequenceDeclaration(const CycleDelayPlace& place) {
  return std::string(place.name).find("sequence declaration") !=
         std::string::npos;
}

template <typename Places>
void ExpectPlacesReport(const Places& places,
                        std::initializer_list<const char*> forms,
                        bool (*chosen)(const CycleDelayPlace&)) {
  for (const auto& place : places) {
    if (!chosen(place)) continue;
    for (const char* form : forms) {
      auto r = Parse(WithCycleDelay(place.source, form));
      EXPECT_TRUE(ReportedError(r.diags, kMinTypMax, place.line, "16.7"))
          << place.name << ": " << form;
    }
  }
}

bool AnyPlace([[maybe_unused]] const CycleDelayPlace& place) { return true; }

bool OutsideASequenceDeclaration(const CycleDelayPlace& place) {
  return !InASequenceDeclaration(place);
}

const auto kAcceptedPrimaries = {"##(2)",   "##(DLY)",     "##(SEL ? 1 : 2)",
                                 "##((2))", "##(1 + (2))", "##(SEL ? (1) : 2)"};

TEST(CycleDelayMinTypMax, EveryPlaceAcceptsAPrimaryWithoutATriple) {
  ExpectEveryPlaceAccepts(kCycleDelayPlaces, kAcceptedPrimaries);
  ExpectEveryPlaceAccepts(kMoreCycleDelayPlaces, kAcceptedPrimaries);
}

const auto kFlatTriples = {"##(1:2:3)", "##(MIN_D:TYP_D:MAX_D)"};

TEST(CycleDelayMinTypMax, EverySequenceDeclarationReportsAFlatTriple) {
  ExpectPlacesReport(kCycleDelayPlaces, kFlatTriples, InASequenceDeclaration);
  ExpectPlacesReport(kMoreCycleDelayPlaces, kFlatTriples,
                     InASequenceDeclaration);
}

TEST(CycleDelayMinTypMax, DISABLED_EveryOtherPlaceReportsAFlatTriple) {
  ExpectPlacesReport(kCycleDelayPlaces, kFlatTriples,
                     OutsideASequenceDeclaration);
  ExpectPlacesReport(kMoreCycleDelayPlaces, kFlatTriples,
                     OutsideASequenceDeclaration);
}

const auto kNestedTriples = {"##((1:2:3))", "##(1 + (1:2:3))",
                             "##(SEL ? (1:2:3) : 2)"};

TEST(CycleDelayMinTypMax, DISABLED_EveryPlaceReportsANestedTriple) {
  ExpectPlacesReport(kCycleDelayPlaces, kNestedTriples, AnyPlace);
  ExpectPlacesReport(kMoreCycleDelayPlaces, kNestedTriples, AnyPlace);
}

}  // namespace
