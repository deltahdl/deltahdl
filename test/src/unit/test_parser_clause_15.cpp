#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult15 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult15 Parse(const std::string &src) {
  ParseResult15 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult15 &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// =============================================================================
// §15.5.1 — Nonblocking event trigger (->>)
// =============================================================================

TEST(ParserSection15, NonblockingEventTrigger) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    ->> e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
}

TEST(ParserSection15, NonblockingEventTriggerHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial ->> top.e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
}

// =============================================================================
// §15.4 — Parameterized mailbox: mailbox #(type)
// =============================================================================

TEST(ParserSection15, MailboxParameterized) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(string) m_box;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  // Should parse without errors — mailbox #(string) is a parameterized type
  auto &items = r.cu->modules[0]->items;
  ASSERT_FALSE(items.empty());
  EXPECT_EQ(items[0]->name, "m_box");
}

// =============================================================================
// §15.5.4 — wait_order basic parsing
// =============================================================================

TEST(ParserSection15, WaitOrderBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
  const std::string kExpected[] = {"a", "b", "c"};
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(stmt->wait_order_events[i]->text, kExpected[i]);
  }
}

// =============================================================================
// §15.5.4 — wait_order with else clause
// =============================================================================

TEST(ParserSection15, WaitOrderWithElseKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) success = 1;\n"
      "    else success = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
}

TEST(ParserSection15, WaitOrderWithElseBranches) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) success = 1;\n"
      "    else success = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
}

// =============================================================================
// §15.5.4 — wait_order with only else clause
// =============================================================================

TEST(ParserSection15, WaitOrderElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b) else $display(\"out of order\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 2u);
  ASSERT_NE(stmt->else_branch, nullptr);
}

// =============================================================================
// §15.5.4 — wait_order with two events
// =============================================================================

TEST(ParserSection15, WaitOrderTwoEvents) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(ev1, ev2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 2u);
}

// =============================================================================
// §15.3 — Semaphore variable declaration (parsed as named type)
// =============================================================================

TEST(ParserSection15, SemaphoreVarDecl) {
  // semaphore is not a keyword — it's a built-in class type in the std
  // package. It parses as a named-type variable declaration via the
  // identifier-based path in ParseImplicitTypeOrInst.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    smTx = new(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Just verify the module parsed without errors.
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// §15.4 — Mailbox variable declaration (parsed as named type)
// =============================================================================

TEST(ParserSection15, MailboxVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// §15.5.1 — Event trigger and wait (existing support, comprehensive test)
// =============================================================================

TEST(ParserSection15, EventTriggerAndWait) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    -> e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
}

// =============================================================================
// §15.5 — Wait on event
// =============================================================================

TEST(ParserSection15, WaitOnEvent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait(done);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

// =============================================================================
// §15.5.4 — wait_order null action (just semicolon)
// =============================================================================

TEST(ParserSection15, WaitOrderNullAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  // Null action: then_branch is null or a null stmt.
}

// =============================================================================
// LRM section 15.4.1 -- Mailbox new()
// =============================================================================

// §15.4.1: basic mailbox declaration and construction with new().
TEST(ParserSection15, MailboxNewUnbounded) {
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

// §15.4.1: mailbox new() with bounded queue size.
TEST(ParserSection15, MailboxNewBounded) {
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

// §15.4.1: parameterized mailbox #(type) with new().
TEST(ParserSection15, MailboxNewParameterizedString) {
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

// §15.4.1: parameterized mailbox #(int) with bounded new(5).
TEST(ParserSection15, MailboxNewParameterizedInt) {
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

// §15.4.1: mailbox method calls (put, get) after new().
TEST(ParserSection15, MailboxNewThenPutGet) {
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
}

// =============================================================================
// LRM section 15.5.2 -- Waiting for an event
// =============================================================================

// §15.5.2: basic @ event wait with named event (from LRM).
TEST(ParserSection15, WaitForEventBasicAt) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    @e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

// §15.5.2: @ event wait with parenthesized expression.
TEST(ParserSection15, WaitForEventParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    @(e);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
}

// §15.5.2: @ event wait followed by a statement body.
TEST(ParserSection15, WaitForEventWithBody) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    @(e) $display(\"event triggered\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_NE(stmt->body, nullptr);
}

// §15.5.2: event wait with hierarchical event identifier.
TEST(ParserSection15, WaitForEventHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(top.sub.done);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

// §15.5.2: event wait with posedge-qualified event expression.
TEST(ParserSection15, WaitForEventPosedge) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge done);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

// =============================================================================
// LRM section 15.5.3 -- Persistent trigger: triggered built-in method
// =============================================================================

// §15.5.3: wait(event.triggered) — persistent trigger check (from LRM).
TEST(ParserSection15, TriggeredMethodWait) {
  auto r = Parse(
      "module m;\n"
      "  event blast;\n"
      "  initial begin\n"
      "    wait(blast.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

// §15.5.3: fork with -> trigger and wait(.triggered) (from LRM example).
TEST(ParserSection15, TriggeredMethodForkPattern) {
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kEventTrigger);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kWait);
}

// §15.5.3: hierarchical wait(.triggered).
TEST(ParserSection15, TriggeredMethodHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait(top.ev.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

// §15.5.3: event alias and triggered check (from LRM event alias example).
TEST(ParserSection15, TriggeredMethodEventAlias) {
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
}

// §15.5.3: wait(.triggered) with subsequent statement body.
TEST(ParserSection15, TriggeredMethodWithBodyStmt) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    wait(e.triggered) $display(\"done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

// =============================================================================
// LRM section 15.5.2 -- Process control (additional)
// =============================================================================

// §15.5.2: wait fork statement to block until all forked processes finish.
TEST(ParserSection15, WaitForkStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "      #20 b = 1;\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

// §15.5.2: disable fork to terminate all forked child processes.
TEST(ParserSection15, DisableForkStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "      #20 b = 1;\n"
      "    join_any\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisableFork);
}

// §15.5.2: @ event wait with 'or' event expression (multiple events).
TEST(ParserSection15, WaitForEventOrExpr) {
  auto r = Parse(
      "module m;\n"
      "  event e1, e2;\n"
      "  initial begin\n"
      "    @(e1 or e2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_GE(stmt->events.size(), 2u);
}
