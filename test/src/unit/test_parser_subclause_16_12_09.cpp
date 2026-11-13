#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_property_spec_places.h"
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

TEST(FollowedByPropertyParsing, OverlappedFollowedBy) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##1 b #-# c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(FollowedByPropertyParsing, NonoverlappedFollowedBy) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req #=# gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(FollowedByPropertyParsing, FollowedByInCoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b #-# c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kCoverProperty));
}

TEST(FollowedByPropertyParsing, FollowedByWithRangedAntecedent) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##[1:2] b #=# c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(FollowedByPropertyParsing, OverlappedFollowedByWithPropertyConsequent) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) ##[0:5] done #-# always !rst);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(FollowedByPropertyParsing, NonoverlappedFollowedByWithPropertyConsequent) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) ##[0:5] done #=# always !rst);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(FollowedByPropertyParsing, ASequenceAntecedentAndAnyConsequentAreRead) {
  for (const char* place : kPropertySpecPlaces) {
    for (const char* spec :
         {"a #-# b", "a #=# b", "##[0:5] a #-# always !b",
          "##[0:5] a #=# always !b", "(a ##1 b) #-# c", "a[*0:1] #=# c",
          "(a or b) #-# (c |-> d)", "first_match(a ##[1:2] b) #=# not c",
          "a #-# strong(b ##1 c)", "a #=# b #-# c", "a #-# (b implies c)",
          "a #=# nexttime b", "a #-# if (b) c else d", "not (a #-# b)",
          "(a #=# b) and c", "a |-> b #-# c"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(PropertySpecIn(place, spec));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

TEST(FollowedByPropertyParsing, APropertyAsTheAntecedentIsReportedInEachPlace) {
  for (const char* place : kPropertySpecPlaces) {
    for (const char* spec :
         {"(a |-> b) #-# c", "(a #=# b) #=# c", "(not a) #-# b",
          "(a until b) #=# c", "(always a) #-# b", "(a iff b) #=# c",
          "(nexttime a) #-# b", "strong(a ##1 b) #=# c"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(PropertySpecIn(place, spec));
      EXPECT_TRUE(ReportedError(
          r.diags, "a property stands where the grammar admits only a sequence",
          3, "A.2.10"));
    }
  }
}

TEST(FollowedByPropertyParsing,
     AFollowedByAsASequenceOperandIsReportedInEachPlace) {
  for (const char* place : kPropertySpecPlaces) {
    for (const char* spec :
         {"(a #-# b) ##1 c", "a ##1 (b #=# c)", "(a #-# b)[*2]",
          "(a #=# b) intersect c", "first_match(a #-# b)", "strong(a #=# b)",
          "(a #-# b) |-> c", "(a #-# b, d = 1)"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      auto r = Parse(PropertySpecIn(place, spec));
      EXPECT_TRUE(ReportedError(r.diags, "the grammar admits", 3, "A.2.10"));
    }
  }
}

TEST(FollowedByPropertyParsing, AFollowedByInASequenceDeclarationIsReported) {
  for (const char* body : {"a #-# b", "a ##1 b #=# c"}) {
    for (const char* scope : {"module", "interface", "package"}) {
      SCOPED_TRACE(std::string(scope) + " " + body);
      auto r = Parse(std::string(scope) +
                     " m;\n  logic clk; bit a, b, c;\n  sequence s; " + body +
                     "; endsequence\nend" + scope + "\n");
      EXPECT_TRUE(ReportedError(r.diags, "the grammar admits", 3, "A.2.10"));
    }
  }
}

}  // namespace
