// §15.5.3: Persistent trigger: triggered built-in method

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- Test helpers ---
namespace {

// =============================================================================
// LRM section 15.5.3 -- Persistent trigger: triggered built-in method
// =============================================================================
// §15.5.3: wait(event.triggered) — persistent trigger check (from LRM).
TEST(ParserSection15, TriggeredMethodWait) {
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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

} // namespace
