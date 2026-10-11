#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;
namespace {

TEST(EventOrOperatorParsing, EventControlMultipleOrExpressions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(a or b or c) x = a + b + c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_GE(stmt->events.size(), 3u);
}

TEST(EventOrOperatorParsing, EventControlMixedEdgesComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk, negedge rst, a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_GE(stmt->events.size(), 3u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kNone);
}

TEST(EventOrOperatorParsing, OrInAlwaysSensitivityList) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, rst, a;\n"
      "  always @(posedge clk or negedge rst) begin\n"
      "    if (!rst)\n"
      "      a <= 0;\n"
      "    else\n"
      "      a <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
}

TEST(EventOrOperatorParsing, OrWithNamedEvents) {
  auto r = Parse(
      "module m;\n"
      "  event e1, e2;\n"
      "  initial begin\n"
      "    @(e1 or e2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_GE(stmt->events.size(), 2u);
}
TEST(EventOrOperatorParsing, EventExprMixedOrComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(a or b, c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 3u);
}

TEST(EventOrOperatorParsing, EventExprMultipleEdgesOrComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge a or negedge b, edge c or d) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 4u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kEdge);
  EXPECT_EQ(stmt->events[3].edge, Edge::kNone);
}

TEST(EventOrOperatorParsing, ParenthesizedOrGroupWithComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @((posedge a or negedge b), c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 3u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kNone);
}

TEST(EventOrOperatorParsing, FiveSignalCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  always @(a, b, c, d, e) x = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 5u);
  for (size_t i = 0; i < 5; ++i) {
    EXPECT_EQ(item->sensitivity[i].edge, Edge::kNone) << "event " << i;
  }
}

// §9.4.2.1: a comma-separated sensitivity list shall be synonymous to the
// or-separated form. Parse both spellings of the same list and confirm
// ParseEventList yields structurally identical event vectors.
TEST(EventOrOperatorParsing, CommaListSynonymousWithOrList) {
  auto parse_events = [](const char* sens) {
    std::string src =
        "module m;\n"
        "  initial begin\n"
        "    @(";
    src += sens;
    src +=
        ") x = 1;\n"
        "  end\n"
        "endmodule\n";
    return Parse(src);
  };

  auto comma = parse_events("a, b, c");
  auto ored = parse_events("a or b or c");
  ASSERT_NE(comma.cu, nullptr);
  ASSERT_NE(ored.cu, nullptr);
  EXPECT_FALSE(comma.has_errors);
  EXPECT_FALSE(ored.has_errors);

  auto* comma_stmt = FirstInitialStmt(comma);
  auto* or_stmt = FirstInitialStmt(ored);
  ASSERT_NE(comma_stmt, nullptr);
  ASSERT_NE(or_stmt, nullptr);
  EXPECT_EQ(comma_stmt->kind, StmtKind::kEventControl);
  EXPECT_EQ(or_stmt->kind, StmtKind::kEventControl);

  ASSERT_EQ(comma_stmt->events.size(), or_stmt->events.size());
  ASSERT_EQ(comma_stmt->events.size(), 3u);
  for (size_t i = 0; i < comma_stmt->events.size(); ++i) {
    EXPECT_EQ(comma_stmt->events[i].edge, or_stmt->events[i].edge)
        << "event " << i;
    EXPECT_EQ(comma_stmt->events[i].signal != nullptr,
              or_stmt->events[i].signal != nullptr)
        << "event " << i;
    EXPECT_EQ(comma_stmt->events[i].iff_condition != nullptr,
              or_stmt->events[i].iff_condition != nullptr)
        << "event " << i;
  }
}

TEST(EventOrOperatorParsing, InterleavedOrGroupsWithComma) {
  auto r = Parse(
      "module m;\n"
      "  always @(a or b, c, d or e) x = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 5u);
}

// Syntax 9-4 lets an event_expression be a parenthesized event_expression, so
// a group of or-ed or comma-separated events, or one event with its iff, stands
// in parentheses whatever its first operand is, and a group may be
// parenthesized again. Parentheses holding none of
// `or`, `,` or `iff` at their own level of nesting are part of an expression,
// a select or a concatenation inside them included.
TEST(EventOrOperatorParsing, AParenthesizedGroupOpensWithAnyOperand) {
  auto r = Parse(
      "module m;\n"
      "  initial @((a or b) or c) x = 1;\n"
      "  initial @((a, b) or posedge c) x = 2;\n"
      "  initial @((a iff en) or b) x = 3;\n"
      "  initial @((v[0] or w[1]) or c) x = 4;\n"
      "  initial @(({a, b}) or c) x = 5;\n"
      "  initial @((a + b) * c) x = 6;\n"
      "  initial @(((posedge a)) or b) x = 7;\n"
      "  initial @(((negedge a)) or b) x = 8;\n"
      "  initial @(((edge a)) or b) x = 9;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  std::vector<const Stmt*> controls;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock)
      controls.push_back(item->body);
  }
  ASSERT_EQ(controls.size(), 9u);
  const std::size_t kCounts[] = {3, 3, 2, 3, 2, 1, 2, 2, 2};
  for (std::size_t i = 0; i < controls.size(); ++i) {
    ASSERT_EQ(controls[i]->kind, StmtKind::kEventControl) << i;
    EXPECT_EQ(controls[i]->events.size(), kCounts[i]) << i;
  }
  EXPECT_EQ(controls[0]->events[0].signal->kind, ExprKind::kIdentifier);
  EXPECT_EQ(controls[1]->events[2].edge, Edge::kPosedge);
  EXPECT_NE(controls[2]->events[0].iff_condition, nullptr);
  EXPECT_EQ(controls[3]->events[0].signal->kind, ExprKind::kSelect);
  EXPECT_EQ(controls[4]->events[0].signal->kind, ExprKind::kConcatenation);
  EXPECT_EQ(controls[5]->events[0].signal->kind, ExprKind::kBinary);
  EXPECT_EQ(controls[6]->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(controls[7]->events[0].edge, Edge::kNegedge);
  EXPECT_EQ(controls[8]->events[0].edge, Edge::kEdge);
}

// A group the source leaves unclosed is reported rather than read past the end
// of the file.
TEST(EventOrOperatorParsing, AnUnclosedGroupIsReported) {
  auto r = Parse("module m; initial @((a or b");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
