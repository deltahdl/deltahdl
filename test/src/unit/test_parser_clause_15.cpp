// §15 Interprocess synchronization and communication — parser tests.

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// §15.3 Semaphores
// ---------------------------------------------------------------------------

TEST(ParserIpcSync, SemaphoreVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  semaphore smTx;\n"
      "  initial begin\n"
      "    smTx = new(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserIpcSync, SemaphoreMethodCalls) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem = new(1);\n"
      "  initial begin\n"
      "    sem.get();\n"
      "    sem.put();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST_F(AnnexHParseTest, SemaphoreAllMethods) {
  auto* unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.get(1);\n"
      "    sem.put(1);\n"
      "    if (sem.try_get(1)) begin\n"
      "      $display(\"acquired\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// ---------------------------------------------------------------------------
// §15.4 Mailboxes
// ---------------------------------------------------------------------------

TEST(ParserIpcSync, MailboxVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserIpcSync, MailboxNewUnbounded) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_GE(r.cu->modules[0]->items.size(), 1u);
}

TEST(ParserIpcSync, MailboxNewBounded) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "  initial begin\n"
      "    mbx = new(10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserIpcSync, MailboxPutAndGet) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(int) mbx;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "    mbx.put(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
}

// §15.4.9 Parameterized mailboxes

TEST(ParserIpcSync, MailboxParameterizedString) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(string) m_box;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  auto& items = r.cu->modules[0]->items;
  ASSERT_FALSE(items.empty());
  EXPECT_EQ(items[0]->name, "m_box");
}

TEST(ParserIpcSync, MailboxParameterizedNewString) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(string) sm;\n"
      "  initial begin\n"
      "    sm = new;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_FALSE(r.cu->modules[0]->items.empty());
}

TEST(ParserIpcSync, MailboxParameterizedNewInt) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(int) mbx;\n"
      "  initial begin\n"
      "    mbx = new(5);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserIpcSync, MailboxParameterizedUsage) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(int) mb = new();\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// ---------------------------------------------------------------------------
// §15.5 Named events
// ---------------------------------------------------------------------------

// §15.5.1 Triggering an event

TEST(ParserIpcSync, EventTriggerBlocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(ParserIpcSync, EventTriggerNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(ParserIpcSync, NonblockingEventTriggerWithDecl) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    ->> e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
}

TEST(ParserIpcSync, NonblockingEventTriggerHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial ->> top.e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
}

TEST(ParserIpcSync, EventTriggerWithDeclaredEvent) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    -> e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
}

TEST(ParserIpcSync, EventTriggerNamedIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> my_event;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
}

TEST(ParserIpcSync, NonblockingEventTriggerNamedIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> my_event;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
}

TEST(ParserIpcSync, EventTriggerInProceduralBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    -> done_event;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

// §15.5.2 Waiting for an event

TEST(ParserIpcSync, WaitForEventWithBody) {
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

TEST(ParserIpcSync, WaitForEventHierarchical) {
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

// §15.5.3 Persistent trigger: triggered built-in method

TEST(ParserIpcSync, TriggeredMethodWait) {
  auto r = Parse(
      "module m;\n"
      "  event blast;\n"
      "  initial begin\n"
      "    wait(blast.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ParserIpcSync, TriggeredMethodForkPattern) {
  auto r = Parse(
      "module m;\n"
      "  event blast;\n"
      "  initial begin\n"
      "    fork\n"
      "      -> blast;\n"
      "      wait(blast.triggered);\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kEventTrigger);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kWait);
}

TEST(ParserIpcSync, TriggeredMethodHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait(top.ev.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ParserIpcSync, TriggeredMethodEventAlias) {
  auto r = Parse(
      "module m;\n"
      "  event done;\n"
      "  event done_too;\n"
      "  initial begin\n"
      "    fork\n"
      "      @done_too;\n"
      "      #1 -> done;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
}

TEST(ParserIpcSync, TriggeredMethodWithBodyStmt) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    wait(e.triggered) $display(\"done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

// §15.5.4 Event sequencing: wait_order()

TEST(ParserIpcSync, WaitOrderBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
  const std::string kExpected[] = {"a", "b", "c"};
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(stmt->wait_order_events[i]->text, kExpected[i]);
  }
}

TEST(ParserIpcSync, WaitOrderWithActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order (a, b, c) $display(\"ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
}

TEST(ParserIpcSync, WaitOrderWithElseDisplay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order (a, b) else $display(\"out of order\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
}

TEST(ParserIpcSync, WaitOrderWithThenAndElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) success = 1;\n"
      "    else success = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
  ASSERT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
}

TEST(ParserIpcSync, WaitOrderTwoEvents) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(ev1, ev2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 2u);
}

TEST(ParserIpcSync, WaitOrderNullAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
}

TEST(ParserIpcSync, WaitOrderWithActionOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b) success = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->then_branch, nullptr);
}

TEST(ParserIpcSync, WaitOrderElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b)\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// §15.5.5 Operations on named event variables

TEST(ParserIpcSync, EventAssignmentMerge) {
  auto r = Parse(
      "module m;\n"
      "  event a, b;\n"
      "  initial begin\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
}

TEST(ParserIpcSync, EventAssignNull) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    e = null;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
}

TEST(ParserIpcSync, EventCompareEquality) {
  auto r = Parse(
      "module m;\n"
      "  event a, b;\n"
      "  initial begin\n"
      "    if (a == b) $display(\"same\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserIpcSync, EventCompareNull) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    if (e == null) $display(\"null\");\n"
      "    if (e != null) $display(\"not null\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserIpcSync, EventCaseEquality) {
  auto r = Parse(
      "module m;\n"
      "  event a, b;\n"
      "  initial begin\n"
      "    if (a === b) $display(\"case eq\");\n"
      "    if (a !== b) $display(\"case neq\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserIpcSync, EventBooleanTest) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    if (e) $display(\"not null\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
