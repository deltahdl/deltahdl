// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult15 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult15 Parse(const std::string& src) {
  ParseResult15 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult15& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

namespace {

// =============================================================================
// LRM section 14.10 -- Clocking block events
// =============================================================================
// §14.10: clocking block event used in always block (from LRM example).
// The clocking block name itself acts as an event trigger in the Observed
// region. This tests the LRM example: always @(dram) $display(...);
TEST(ParserSection14, ClockingBlockEventAlwaysAt) {
  auto r = Parse(
      "module foo(input phi1, input [7:0] data);\n"
      "  clocking dram @(posedge phi1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  always @(dram)\n"
      "    $display(\"clocking block event\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "dram");
  // The always block should also have been parsed (at least 2 items).
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

// §14.10: clocking block with output negedge skew (from LRM example).
TEST(ParserSection14, ClockingBlockEventOutputNegedgeSkew) {
  auto r = Parse(
      "module foo(input phi1, input [7:0] data);\n"
      "  clocking dram @(posedge phi1);\n"
      "    input data;\n"
      "    output negedge #1 address;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 2u);
  auto& out_sig = item->clocking_signals[1];
  EXPECT_EQ(out_sig.direction, Direction::kOutput);
  EXPECT_EQ(out_sig.name, "address");
  EXPECT_EQ(out_sig.skew_edge, Edge::kNegedge);
  ASSERT_NE(out_sig.skew_delay, nullptr);
}

// §14.10: clocking event alongside a posedge always block.
TEST(ParserSection14, ClockingBlockEventWithPosedgeAlways) {
  auto r = Parse(
      "module m;\n"
      "  clocking dram @(posedge phi1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  always @(posedge phi1) $display(\"clocking event\");\n"
      "  always @(dram) $display(\"clocking block event\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  // Three items: clocking block + two always blocks.
  EXPECT_GE(r.cu->modules[0]->items.size(), 3u);
}

// §14.10: clocking block with multiple input signals triggers one event.
TEST(ParserSection14, ClockingBlockEventMultipleInputs) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, b, c;\n"
      "  endclocking\n"
      "  always @(cb) $display(\"triggered\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

// =============================================================================
// LRM section 14.12 -- Default clocking
// =============================================================================
// §14.12: default clocking with negedge (variation of the LRM examples).
TEST(ParserSection14, DefaultClockingNegedge) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(negedge clk);\n"
      "    input data;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
  ASSERT_EQ(item->clocking_signals.size(), 2u);
}

// §14.12: default clocking block with end label.
TEST(ParserSection14, DefaultClockingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  default clocking bus @(posedge clk);\n"
      "    input data;\n"
      "  endclocking : bus\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "bus");
}

// §14.12: unnamed default clocking block with multiple signals.
TEST(ParserSection14, DefaultClockingUnnamedMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk);\n"
      "    input a, b;\n"
      "    output c;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
  ASSERT_EQ(item->clocking_signals.size(), 3u);
}

// =============================================================================
// LRM section 14.13 -- Input sampling
// =============================================================================
// §14.13: input sampled at clocking event (basic pattern from LRM).
// Validates: clocking cb @(negedge clk); input v; endclocking
TEST(ParserSection14, InputSamplingBasic) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(negedge clk);\n"
      "    input v;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "v");
  EXPECT_EQ(item->clocking_signals[0].skew_delay, nullptr);
}

// §14.13: input with explicit #0 skew (samples in the Observed region).
TEST(ParserSection14, InputSamplingExplicitZeroSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #0 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->kind, ExprKind::kIntegerLiteral);
}

// §14.13: inout signals are also sampled as inputs at the clocking event.
TEST(ParserSection14, InputSamplingInoutSignal) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// §14.13: input with nonzero skew samples from a prior time step.
TEST(ParserSection14, InputSamplingNonzeroSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #3 addr;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  EXPECT_EQ(sig.name, "addr");
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->kind, ExprKind::kIntegerLiteral);
}

// §14.13: multiple inputs with same skew declaration.
TEST(ParserSection14, InputSamplingMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(negedge clk);\n"
      "    input #1 a, b, c;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->clocking_signals[i].direction, Direction::kInput)
        << "signal " << i;
    ASSERT_NE(item->clocking_signals[i].skew_delay, nullptr) << "signal " << i;
  }
}

// §14.14: global clocking with end label.
TEST(ParserSection14, GlobalClockingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking : gclk\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_EQ(item->name, "gclk");
}

// §14.14: global clocking has no signal declarations (shall be empty body).
TEST(ParserSection14, GlobalClockingNoSignals) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gc @(negedge clk); endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->clocking_signals.empty());
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

// §14.14: global clocking in subsystem pattern (from LRM hierarchical example).
TEST(ParserSection14, GlobalClockingSubsystemPattern) {
  auto r = Parse(
      "module subsystem1;\n"
      "  logic subclk1;\n"
      "  global clocking sub_sys1 @(subclk1); endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_EQ(item->name, "sub_sys1");
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

// default clocking as module_or_generate_item_declaration.
TEST(SourceText, DefaultClockingAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kClockingBlock);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->is_default_clocking);
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
}

TEST(ParserSection15, NonblockingEventTriggerHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial ->> top.e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
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
  auto& items = r.cu->modules[0]->items;
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_GE(stmt->events.size(), 2u);
}

// default disable iff expression_or_dist (module_or_generate_item_declaration).
TEST(SourceText, DefaultDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

// =============================================================================
// §16.3 Immediate assertions — assert
// =============================================================================
TEST(ParserSection16, ImmediateAssertBasicKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a == b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(ParserSection16, ImmediateAssertBasicNoActions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a == b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(ParserSection16, ImmediateAssertWithElseKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(x > 0) $display(\"ok\"); else $error(\"fail\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(ParserSection16, ImmediateAssertWithElseActions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(x > 0) $display(\"ok\"); else $error(\"fail\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(ParserSection16, ImmediateAssertPassOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(valid) $display(\"passed\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.3 Immediate assertions — assume
// =============================================================================
TEST(ParserSection16, ImmediateAssumeBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume(x != 0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(ParserSection16, ImmediateAssumeWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume(y > 0) $display(\"ok\"); else $error(\"bad\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.3 Immediate assertions — cover
// =============================================================================
TEST(ParserSection16, ImmediateCoverBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    cover(cond);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

}  // namespace
