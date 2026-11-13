#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_property_spec_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ImpliesIffParsing, ImpliesAndIffTakeAnyPropertyInEachPlace) {
  for (const char* place : kPropertySpecPlaces) {
    for (const char* spec :
         {"a implies b", "a iff b", "a ##1 b implies c ##1 d",
          "a ##[1:2] b iff c", "(a |-> b) implies (c |=> d)", "not a iff b",
          "(nexttime a) implies b", "a iff (always b)",
          "(a until b) implies (s_eventually c)", "strong(a ##1 b) iff d",
          "(a implies b) iff (c implies d)", "(a iff b) implies c",
          "if (a) b else c iff d", "a |-> (b implies c)", "not (a iff b)",
          "@(posedge clk iff d) a iff b"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(PropertySpecIn(place, spec));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

TEST(ImpliesIffParsing, ImpliesOrIffAsASequenceOperandIsReportedInEachPlace) {
  for (const char* place : kPropertySpecPlaces) {
    for (const char* spec :
         {"(a implies b) ##1 c", "a ##1 (b iff c)", "(a implies b)[*2]",
          "(a iff b) intersect c", "a within (b implies c)",
          "first_match(a iff b)", "strong(a implies b)", "(a iff b) |-> c",
          "(a implies b) |=> c", "(a iff b) #-# c", "(a implies b, d = 1)"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(PropertySpecIn(place, spec));
      EXPECT_TRUE(ReportedError(r.diags, "the grammar admits", 3, "A.2.10"));
    }
  }
}

TEST(ImpliesIffParsing, ImpliesOrIffInASequenceDeclarationIsReported) {
  for (const char* body : {"a implies b", "a iff b", "a ##1 b iff c"}) {
    for (const char* scope : {"module", "interface", "package"}) {
      SCOPED_TRACE(std::string(scope) + " " + body);
      auto r = Parse(std::string(scope) +
                     " m;\n  logic clk; bit a, b, c;\n  sequence s; " + body +
                     "; endsequence\nend" + scope + "\n");
      EXPECT_TRUE(ReportedError(r.diags, "the grammar admits", 3, "A.2.10"));
    }
  }
}

TEST(ImpliesIffParsing, ImpliesOrIffWithAMissingOperandIsReported) {
  for (const char* spec : {"a implies", "iff b", "a iff iff b", "implies b"}) {
    SCOPED_TRACE(spec);
    auto r = Parse(PropertySpecIn("module", spec));
    EXPECT_TRUE(ReportedError(r.diags, "the grammar admits", 3, "A.2.10"));
  }
}

}  // namespace
