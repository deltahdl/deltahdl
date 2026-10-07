#include <gtest/gtest.h>

#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CovergroupWithCross) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint a;
        coverpoint b;
        cross a, b;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// §19.6 / Syntax 19-4: list_of_cross_items requires at least two cross_items,
// so a one-item `cross a;` is rejected.
TEST_F(VerifyParseTest, SingleItemCrossIsError) {
  Parse(R"(
    module m;
      covergroup cg;
        coverpoint a;
        cross a;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "a cross shall list at least two coverage points",
                            5, "19.6"));
}

// §19.6: a cross names coverage points or variables, so an expression has to
// become a coverage point before it can be crossed, and `cross a + b, c;` is
// rejected.
TEST_F(VerifyParseTest, ExpressionCrossItemIsError) {
  Parse(R"(
    module m;
      covergroup cg;
        coverpoint a;
        coverpoint b;
        coverpoint c;
        cross a + b, c;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(
      ReportedError(diag_.Diagnostics(),
                    "a cross item names a coverage point or a variable; to "
                    "cross an expression, give it a coverage point first",
                    7, "19.6"));
}

// §19.6: the cross label is optional and, when present, precedes the
// two-or-more item list. A labeled two-item cross parses without error.
TEST_F(VerifyParseTest, LabeledCrossParsesWithoutError) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint a;
        coverpoint b;
        axb : cross a, b;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// §19.6: a cross generalizes to more than two coverage points; a three-item
// cross with an `iff` guard parses without error.
TEST_F(VerifyParseTest, ThreeItemCrossWithIffParsesWithoutError) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint a;
        coverpoint b;
        coverpoint c;
        cross a, b, c iff (enable);
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// §19.6.1.4 with A.2.11: a cross bin may select with a cross_set_expression,
// an expression yielding the tuples of the bin, so an assignment pattern
// stands there, and a function declared in the cross body may build one; the
// '{ of a pattern is no brace of the cross body.
TEST_F(VerifyParseTest, CrossSetExpressionAssignmentPatternsParse) {
  auto* unit = Parse(R"(
    module m;
      logic [31:0] a, b;
      covergroup cg(int cg_lim);
        coverpoint a;
        coverpoint b;
        aXb : cross a, b {
          option.cross_retain_auto_bins = 0;
          function CrossQueueType myFunc1(int f_lim);
            for (int i = 0; i < f_lim; ++i) myFunc1.push_back('{i, i});
          endfunction
          bins one = myFunc1(cg_lim);
          bins two = '{ '{1, 1}, '{2, 2} };
        }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  const CovergroupDecl* cg = nullptr;
  for (const ModuleItem* item : unit->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) cg = item->covergroup;
  }
  ASSERT_NE(cg, nullptr);
  ASSERT_EQ(cg->items.size(), 3u);
  const CoverCrossDecl* x = cg->items[2].cover_cross;
  ASSERT_NE(x, nullptr);
  ASSERT_EQ(x->body.size(), 4u);
  EXPECT_EQ(x->body[0].kind, CrossBodyItemKind::kOption);
  EXPECT_EQ(x->body[1].kind, CrossBodyItemKind::kFunction);
  ASSERT_EQ(x->body[2].kind, CrossBodyItemKind::kBinsSelection);
  EXPECT_EQ(x->body[2].bins.select->kind, SelectExpressionKind::kCrossSet);
  ASSERT_EQ(x->body[3].kind, CrossBodyItemKind::kBinsSelection);
  EXPECT_EQ(x->body[3].bins.select->kind, SelectExpressionKind::kCrossSet);
  EXPECT_EQ(x->body[3].bins.select->expr->kind, ExprKind::kAssignmentPattern);
}

// §19.6.1.2 with A.2.11: the clause's own example -- a cross name filtered by
// `with` and `matches`, a parenthesized select filtered by `with`, and two
// filtered selections joined by `||` -- is held on the tree with `with`
// binding to the operand it follows.
TEST_F(VerifyParseTest, CrossBinWithCovergroupExpressionsTree) {
  auto* unit = Parse(R"(
    module m;
      logic [0:7] a, b;
      parameter [0:7] mask = 0;
      covergroup cg;
        coverpoint a {
          bins low[] = {[0:127]};
          bins high = {[128:255]};
        }
        coverpoint b {
          bins two[] = b with (item % 2 == 0);
          bins three[] = b with (item % 3 == 0);
        }
        X: cross a, b {
          bins apple = X with (a + b < 257) matches 127;
          bins cherry = (binsof(b) intersect {[0:50]}
                         && binsof(a.low) intersect {[0:50]}) with (a == b);
          bins plum = binsof(b.two) with (b > 12)
                      || binsof(a.low) with (a & b & mask);
          bins all = X with (a < b) matches $;
        }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  const CovergroupDecl* cg = nullptr;
  for (const ModuleItem* item : unit->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) cg = item->covergroup;
  }
  ASSERT_NE(cg, nullptr);
  ASSERT_EQ(cg->items.size(), 3u);
  EXPECT_EQ(cg->items[1].cover_point->bins[0].kind,
            BinsOrOptionsKind::kCoverPointWith);
  EXPECT_EQ(cg->items[1].cover_point->bins[0].with_cover_point, "b");
  const CoverCrossDecl* x = cg->items[2].cover_cross;
  ASSERT_EQ(x->body.size(), 4u);
  const SelectExpression* apple = x->body[0].bins.select;
  ASSERT_EQ(apple->kind, SelectExpressionKind::kWith);
  EXPECT_EQ(apple->lhs->kind, SelectExpressionKind::kCrossIdentifier);
  EXPECT_EQ(apple->lhs->cross_name, "X");
  EXPECT_NE(apple->matches, nullptr);
  const SelectExpression* cherry = x->body[1].bins.select;
  ASSERT_EQ(cherry->kind, SelectExpressionKind::kWith);
  ASSERT_EQ(cherry->lhs->kind, SelectExpressionKind::kParenthesized);
  EXPECT_EQ(cherry->lhs->lhs->kind, SelectExpressionKind::kAnd);
  const SelectExpression* plum = x->body[2].bins.select;
  ASSERT_EQ(plum->kind, SelectExpressionKind::kOr);
  EXPECT_EQ(plum->lhs->kind, SelectExpressionKind::kWith);
  EXPECT_EQ(plum->rhs->kind, SelectExpressionKind::kWith);
  EXPECT_TRUE(x->body[3].bins.select->matches_dollar);
}

// §19.6 with §19.6.1.4: a cross's name is seen only through a covergroup
// variable or the covergroup's scope, so a lone identifier in its body is the
// cross_identifier only where it is the cross's own label; any other, a queue
// `q` or one in an unlabelled cross, is a cross_set_expression.
TEST_F(VerifyParseTest, LoneIdentifierOtherThanTheCrossLabelIsACrossSet) {
  auto* unit = Parse(R"(
    module m;
      bit [1:0] a, b;
      covergroup cg;
        X: cross a, b {
          bins all = X;
          bins one = q;
          bins two = q with (a == b);
        }
        cross a, b { bins three = X; }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  const CovergroupDecl* cg = nullptr;
  for (const ModuleItem* item : unit->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) cg = item->covergroup;
  }
  ASSERT_NE(cg, nullptr);
  ASSERT_EQ(cg->items.size(), 2u);
  const CoverCrossDecl* x = cg->items[0].cover_cross;
  ASSERT_EQ(x->body.size(), 3u);
  EXPECT_EQ(x->body[0].bins.select->kind,
            SelectExpressionKind::kCrossIdentifier);
  const SelectExpression* one = x->body[1].bins.select;
  ASSERT_EQ(one->kind, SelectExpressionKind::kCrossSet);
  ASSERT_NE(one->expr, nullptr);
  EXPECT_EQ(one->expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(one->expr->text, "q");
  const SelectExpression* two = x->body[2].bins.select;
  ASSERT_EQ(two->kind, SelectExpressionKind::kWith);
  EXPECT_EQ(two->lhs->kind, SelectExpressionKind::kCrossSet);
  const CoverCrossDecl* unnamed = cg->items[1].cover_cross;
  ASSERT_EQ(unnamed->body.size(), 1u);
  EXPECT_EQ(unnamed->body[0].bins.select->kind,
            SelectExpressionKind::kCrossSet);
}

}  // namespace
