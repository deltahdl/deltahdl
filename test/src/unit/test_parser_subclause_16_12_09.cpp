#include "fixture_parser.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// §16.12.9: the overlapped followed-by form `sequence_expr #-# property_expr`
// is accepted at the property level of a concurrent assertion.
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

// §16.12.9: the nonoverlapped followed-by form `sequence_expr #=#
// property_expr` is likewise accepted at the property level of a concurrent
// assertion.
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

// §16.12.9: a followed-by is especially convenient for a cover property over a
// sequence followed by a property, so the form is accepted there too.
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

// §16.12.9: the antecedent of a followed-by is a full sequence_expr, so a
// ranged-delay sequence ahead of the #=# operator is accepted at the property
// level — the realistic "a sequence followed by a property" shape.
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

// §16.12.9: the consequent operand is a property_expr, not merely a Boolean, so
// a compound property on the right of #-# — here an `always` property, the
// consequent shape the clause's own worked examples use — is accepted at the
// property level. The lower precedence of `always` binds the whole followed-by
// as `(seq) #-# (always ...)`.
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

// §16.12.9: the nonoverlapped operator likewise takes a property_expr
// consequent — a compound `always` property after #=# is accepted at the
// property level.
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
