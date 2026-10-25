#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

// A.6.5's delay_control is `#` and a delay_value, and A.2.2.3 gives
// delay_value the form 1step, so a delay statement, an intra-assignment delay
// after `=` and after `<=`, and a nonblocking trigger's delay each take
// `#1step` as the one literal a gate's delay is read as. Read as `#1`, each
// left `step` behind: the delay statement governed a call to a task named
// step, and the others reported the stray name.
TEST(TimingControlSyntaxParsing, OneStepIsADelayValueOfEveryDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  int x, y;\n"
      "  initial begin\n"
      "    #1step;\n"
      "    x = #1step y;\n"
      "    x <= #1step y;\n"
      "    ->> #1step e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 4u);
  for (const Stmt* s : body->stmts) {
    ASSERT_NE(s->delay, nullptr);
    EXPECT_EQ(s->delay->text, "1step");
  }
  ASSERT_NE(body->stmts[0]->body, nullptr);
  EXPECT_EQ(body->stmts[0]->body->kind, StmtKind::kNull);
}

// 1step is a 1 and a step with nothing between them: written apart, by a space
// or by a line break, they are a delay of 1 and the statement it governs, here
// a call to a task named step.
TEST(TimingControlSyntaxParsing, OneAndStepWrittenApartAreADelayAndACall) {
  auto r = Parse(
      "module m;\n"
      "  task step; endtask\n"
      "  initial begin\n"
      "    #1 step;\n"
      "    #1\n"
      "    step;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  for (const Stmt* s : body->stmts) {
    ASSERT_NE(s->delay, nullptr);
    EXPECT_EQ(s->delay->text, "1");
    ASSERT_NE(s->body, nullptr);
    EXPECT_EQ(s->body->kind, StmtKind::kExprStmt);
  }
}

// A.6.5 writes a clocking_event without parentheses as `@` and a name, and
// A.9.3's hierarchical_identifier lets a bit-select stand only before a
// period, so an event control whose name ends in one or more selects is
// reported. A select before a period, and a select inside parentheses, draw
// no report.
TEST(TimingControlSyntaxParsing, AnUnparenthesizedEventEndingInASelect) {
  auto r = Parse(
      "module m;\n"
      "  event arr[2][2];\n"
      "  int n;\n"
      "  initial begin\n"
      "    @arr[1];\n"
      "    @arr[0][1];\n"
      "    @g[1].e;\n"
      "    @(arr[1][0]);\n"
      "  end\n"
      "  always @arr[1] n++;\n"
      "endmodule\n");
  for (uint32_t line : {5u, 6u, 10u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "an unparenthesized clocking event is '@' and a "
                              "name; an expression is parenthesized",
                              line, "A.6.5"));
  }
  EXPECT_EQ(r.diags.size(), 3u);
}

// A.6.5's delay_or_event_control holds an event_control directly or after
// `repeat ( expression )`, and an event_control is `@` and a name, `@*`,
// `@(*)` or a parenthesized event expression. After an assignment operator
// each form is read as an event control statement reads it, and after
// `->> repeat ( expression )` as well. Only the parenthesized event expression
// was read there, so the other forms drew a report that a '(' was missing.
TEST(TimingControlSyntaxParsing, EveryEventControlFollowsAnAssignOrATrigger) {
  auto r = Parse(
      "module m;\n"
      "  event e, ev;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = @e b;\n"
      "    a <= @top.e b;\n"
      "    a = repeat (2) @e b;\n"
      "    a = @* b;\n"
      "    a = @(*) b;\n"
      "    ->> repeat (2) @e ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 6u);
  EXPECT_EQ(body->stmts[0]->events.size(), 1u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(body->stmts[1]->events.size(), 1u);
  EXPECT_NE(body->stmts[2]->repeat_event_count, nullptr);
  EXPECT_EQ(body->stmts[2]->events.size(), 1u);
  EXPECT_TRUE(body->stmts[3]->is_star_event);
  EXPECT_TRUE(body->stmts[4]->is_star_event);
  EXPECT_NE(body->stmts[5]->repeat_event_count, nullptr);
  EXPECT_EQ(body->stmts[5]->events.size(), 1u);
}

// A.6.5 writes a wait_order operand as a hierarchical_identifier, which takes
// bit-selects only before a period, and a bit-select is never a range. An
// operand ending in a select, one with a part-select before its period and
// one reached through the compilation unit's scope are reported; a bit-select
// before a period and a `$root.` name are not.
TEST(TimingControlSyntaxParsing, WaitOrderOperandSelectsStandBeforeAPeriod) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, arr[0]);\n"
      "    wait_order(a, g[1:0].e);\n"
      "    wait_order(a, $unit::e);\n"
      "    wait_order(a, g[1].e);\n"
      "    wait_order(a, $root.m.e);\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {3u, 4u, 5u}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "wait_order operand shall be a hierarchical identifier", line,
        "15.5.4"));
  }
  EXPECT_EQ(r.diags.size(), 3u);
}

// A.6.5 writes a disable statement's target as a hierarchical task or block
// identifier, both A.9.3 hierarchical_identifiers, so an operation, a call, a
// name ending in a select and a name reached through a package scope are
// reported. A name, a dotted name and a bit-select before a period are not.
TEST(TimingControlSyntaxParsing, ADisableTargetIsAHierarchicalName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable a + b;\n"
      "    disable t();\n"
      "    disable blk[0];\n"
      "    disable p::t;\n"
      "    disable blk;\n"
      "    disable top.blk;\n"
      "    disable g[0].blk;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {3u, 4u, 5u, 6u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a disable statement names a task or a block, "
                              "which is a hierarchical identifier",
                              line, "A.6.5"));
  }
  EXPECT_EQ(r.diags.size(), 4u);
}

// A.6.5 writes an event trigger's operand as a hierarchical_event_identifier
// and a nonrange_select, which A.8.4 builds of bit-selects and member selects
// alone. An operation, a call, a part-select, an indexed part-select after
// `->>` and a name reached through a package scope are reported. A name, an
// element of an array of events, a member and a selected member are not.
TEST(TimingControlSyntaxParsing, AnEventTriggerNamesAnEvent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> a + b;\n"
      "    -> f();\n"
      "    -> e[1:0];\n"
      "    ->> e[0+:2];\n"
      "    -> p::e;\n"
      "    -> e;\n"
      "    -> arr[1];\n"
      "    ->> m[\"k\"];\n"
      "    -> h.ev;\n"
      "    -> g[1].e[0];\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {3u, 4u, 5u, 6u, 7u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "an event trigger names an event: a hierarchical "
                              "identifier and its bit-selects",
                              line, "A.6.5"));
  }
  EXPECT_EQ(r.diags.size(), 5u);
}

}  // namespace
