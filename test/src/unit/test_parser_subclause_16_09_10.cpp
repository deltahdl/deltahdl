#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "helpers_sequence_places.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, Within) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##[1:3] b) within (c ##[1:5] d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, WithinContainsRepeatedSequence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (!trdy)[*7] within (start_irdy ##1 (!irdy)[*8]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, WithinContainsIntersectSequence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##1 b) within ((c ##1 d) intersect (e ##2 f)));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

constexpr const char* kPropertyForSequence =
    "a property stands where the grammar admits only a sequence";
constexpr const char* kBodyNotAdmitted =
    "this declaration's body is not one the grammar admits";

TEST(WithinOperands, APropertyOnEitherSideIsReportedInEveryPlace) {
  for (const char* spec :
       {"(a |-> b) within (c ##1 c)", "(not a) within c",
        "(a ##1 b) within (c |=> d)", "c within (a implies b)"}) {
    SCOPED_TRACE(spec);
    auto r = Parse(InEverySequencePlace("@(posedge clk) " + std::string(spec)));
    for (uint32_t line : {3u, 4u}) {
      EXPECT_TRUE(ReportedError(r.diags, kPropertyForSequence, line, "A.2.10"))
          << line;
    }
    for (uint32_t line : {2u, 7u}) {
      EXPECT_TRUE(ReportedError(r.diags, kBodyNotAdmitted, line, "A.2.10"))
          << line;
    }
  }
}

TEST(WithinOperands, ASequenceOnEitherSideIsAcceptedInEveryPlace) {
  for (const char* spec :
       {"(a ##1 b) within (c ##1 c)", "a within c", "(!a) within (c ##[1:3] d)",
        "a[*0:1] within c[*2]", "first_match(a ##[1:2] b) within (c ##3 d)"}) {
    SCOPED_TRACE(spec);
    auto r = Parse(InEverySequencePlace("@(posedge clk) " + std::string(spec)));
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
  }
}

}  // namespace
