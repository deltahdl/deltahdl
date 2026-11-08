#include <gtest/gtest.h>

#include "fixture_parser.h"
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

}  // namespace
