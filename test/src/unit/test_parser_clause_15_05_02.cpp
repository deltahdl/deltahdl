#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(EventWaitParser, WaitForEventWithBody) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    @(e) $display(\"event triggered\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_NE(stmt->body, nullptr);
}

TEST(EventWaitParser, WaitForEventHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(top.sub.done);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

// §15.5.2: The wait syntax is literally "@ hierarchical_event_identifier;"
// — the bare form, no parentheses. The parser must accept it as an
// event-control statement bound to the named event identifier.
TEST(EventWaitParser, BareAtSyntaxBindsToNamedEvent) {
  auto r = Parse(
      "module m;\n"
      "  event ev;\n"
      "  initial @ev ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  auto* stmt = item->body;
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  ASSERT_NE(stmt->events[0].signal, nullptr);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}

// §15.5.2: "hierarchical_event_identifier" in the wait syntax allows the
// named event to be reached through a dotted instance path. Combined with
// the bare form (no parentheses), the parser must build the
// event-control statement with a member-access signal expression.
TEST(EventWaitParser, BareAtSyntaxBindsToHierarchicalNamedEvent) {
  auto r = Parse(
      "module m;\n"
      "  initial @c1.ev ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  auto* stmt = item->body;
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  ASSERT_NE(stmt->events[0].signal, nullptr);
  EXPECT_EQ(stmt->events[0].signal->kind, ExprKind::kMemberAccess);
}

}  // namespace
