#include <gtest/gtest.h>

#include <string>
#include <string_view>

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

ModuleItem* FirstItemOfKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

TEST(AssertionSemanticsParsing, OverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a && b |-> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, NonoverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, SequenceAntecedentOverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) (a ##1 b ##1 c) |-> (d ##1 e));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, NonoverlapImplicationInAssumeProperty) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssumeProperty));
}

TEST(AssertionSemanticsParsing, OverlapImplicationInCoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) start |-> busy);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kCoverProperty));
}

TEST(AssertionSemanticsParsing, ImplicationInNamedPropertyDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    @(posedge clk) a |=> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

TEST(AssertionSemanticsParsing, NestedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b |=> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing,
     ImplicationOperatorDrivesTemporalClassification) {
  const std::string_view kPlaceholder = "<property_spec>";

  auto overlap = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(overlap.cu, nullptr);
  auto* ov = FirstItemOfKind(overlap, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ov, nullptr);
  ASSERT_NE(ov->assert_expr, nullptr);
  EXPECT_EQ(ov->assert_expr->text, kPlaceholder);

  auto nonoverlap = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |=> b);\n"
      "endmodule\n");
  ASSERT_NE(nonoverlap.cu, nullptr);
  auto* no = FirstItemOfKind(nonoverlap, ModuleItemKind::kAssertProperty);
  ASSERT_NE(no, nullptr);
  ASSERT_NE(no->assert_expr, nullptr);
  EXPECT_EQ(no->assert_expr->text, kPlaceholder);

  auto boolean = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a && b);\n"
      "endmodule\n");
  ASSERT_NE(boolean.cu, nullptr);
  auto* bl = FirstItemOfKind(boolean, ModuleItemKind::kAssertProperty);
  ASSERT_NE(bl, nullptr);
  ASSERT_NE(bl->assert_expr, nullptr);
  EXPECT_NE(bl->assert_expr->text, kPlaceholder);
}

constexpr const char* kImplicationPlaces[] = {
    "module",  "procedural", "generate", "interface", "program",
    "checker", "property",   "package",  "unit"};

std::string ImplicationIn(const std::string& place, const std::string& spec) {
  const std::string kSignals = "  logic clk; bit a, b, c, d;\n";
  const std::string kAssertion =
      "  a1: assert property (@(posedge clk) " + spec + ");\n";
  if (place == "procedural") {
    return "module m;\n" + kSignals +
           "  always @(posedge clk) assert property (" + spec +
           ");\nendmodule\n";
  }
  if (place == "generate") {
    return "module m;\n" + kSignals + "  if (1) begin : g" +
           kAssertion.substr(1) + "  end\nendmodule\n";
  }
  if (place == "interface" || place == "program" || place == "checker") {
    return place + " m;\n" + kSignals + kAssertion + "end" + place + "\n";
  }
  const std::string kDeclared = "  property q; " + spec + "; endproperty\n";
  if (place == "property") {
    return "module m;\n" + kSignals + kDeclared + "endmodule\n";
  }
  if (place == "package") {
    return "package pk;\n" + kSignals + kDeclared + "endpackage\n";
  }
  if (place == "unit") return "\n" + kSignals + kDeclared;
  return "module m;\n" + kSignals + kAssertion + "endmodule\n";
}

constexpr const char* kPropertyForSequence =
    "a property stands where the grammar admits only a sequence";

TEST(AssertionSemanticsParsing, APropertyAsTheAntecedentIsReportedInEachPlace) {
  for (const char* place : kImplicationPlaces) {
    for (const char* spec :
         {"(a |-> b) |-> c", "(a |=> b) |=> c", "(not a) |-> b",
          "(a until b) |=> c", "(nexttime a) |-> b", "(always a) |=> b",
          "(a implies b) |-> c", "(a iff b) |=> c", "(a #-# b) |-> c",
          "(s_eventually a) |=> b", "(if (a) b) |-> c",
          "(accept_on (a) b) |=> c", "strong(a ##1 b) |-> c"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(ImplicationIn(place, spec));
      EXPECT_TRUE(ReportedError(r.diags, kPropertyForSequence, 3, "A.2.10"));
    }
  }
}

TEST(AssertionSemanticsParsing, ASequenceAsTheAntecedentIsReadInEachPlace) {
  for (const char* place : kImplicationPlaces) {
    for (const char* spec :
         {"a |-> c", "a |=> c", "(a) |-> c", "(a ##1 b) |-> c",
          "a ##[1:2] b |=> c", "(a or b) |-> c", "(a and b) |=> c",
          "(a intersect b) |-> c", "a[*0:1] |=> c", "b[->1] |-> c",
          "first_match(a ##[1:2] b) |=> c", "a throughout b ##1 c |-> d",
          "(a ##1 b) within (c ##1 d) |=> a", "a ##0 b[*2] |-> ##[3:8] c",
          "a dist {1 := 1} |-> b"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(ImplicationIn(place, spec));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

TEST(AssertionSemanticsParsing,
     AnImplicationAsASequenceOperandIsReportedInEachPlace) {
  for (const char* place : kImplicationPlaces) {
    for (const char* spec :
         {"(a |-> b) ##1 c", "a ##1 (b |=> c)", "(a |-> b)[*2]",
          "(a |=> b)[=1]", "(a |-> b) intersect c", "a within (b |=> c)",
          "a throughout (b |-> c)", "first_match(a |-> b)", "strong(a |=> b)",
          "weak(a |-> b)", "(a |-> b, d = 1)", "(a ##1 b |-> c) ##0 d"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(ImplicationIn(place, spec));
      EXPECT_TRUE(ReportedError(r.diags, "the grammar admits", 3, "A.2.10"));
    }
  }
}

TEST(AssertionSemanticsParsing,
     AnImplicationAsAPropertyOperandIsReadInEachPlace) {
  for (const char* place : kImplicationPlaces) {
    for (const char* spec :
         {"a |-> b |=> c", "a |=> (b |-> c)", "not (a |-> b)",
          "(a |-> b) and c", "(a |=> b) or (c |-> d)", "always (a |-> b)",
          "s_eventually (a |=> b)", "nexttime (a |-> b)",
          "if (a) b |-> c else d |=> c", "(a |-> b) until c",
          "accept_on (d) a |=> b", "(a |-> b) implies (c |=> d)",
          "a #-# (b |-> c)", "a |-> ##[1:5] b && c"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(ImplicationIn(place, spec));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

TEST(AssertionSemanticsParsing, AnImplicationInASequenceDeclarationIsReported) {
  for (const char* body : {"a |-> b", "a ##1 b |=> c", "(a |-> b) ##1 c"}) {
    for (const char* scope : {"module", "interface", "package"}) {
      SCOPED_TRACE(std::string(scope) + " " + body);
      auto r = Parse(std::string(scope) +
                     " m;\n  logic clk; bit a, b, c;\n  sequence s; " + body +
                     "; endsequence\nend" + scope + "\n");
      EXPECT_TRUE(ReportedError(r.diags, "the grammar admits", 3, "A.2.10"));
    }
  }
}

TEST(AssertionSemanticsParsing, AnImplicationInACoverSequenceIsReported) {
  for (const char* spec : {"a |-> b", "a |=> b"}) {
    SCOPED_TRACE(spec);
    auto r = Parse(std::string("module m;\n  logic clk; bit a, b;\n"
                               "  cover sequence (@(posedge clk) ") +
                   spec + ");\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, "the grammar admits", 3, "A.2.10"));
  }
}

}  // namespace
