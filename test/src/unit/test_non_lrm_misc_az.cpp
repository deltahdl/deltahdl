// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

static bool HasItemOfKind(const std::vector<ModuleItem*>& items,
                          ModuleItemKind kind) {
  for (const auto* item : items)
    if (item->kind == kind) return true;
  return false;
}

static ModuleItem* FindItemByKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// LRM §3.6 — Checkers
// =============================================================================
// §3.6: Checker encapsulates assertions (assert property, cover property,
//        property/sequence declarations) — the primary purpose of checkers.
TEST(ParserClause03, Cl3_6_AssertionsInChecker) {
  auto r = ParseWithPreprocessor(
      "checker req_ack_chk(logic clk, req, ack);\n"
      "  property req_followed_by_ack;\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "  assert property (req_followed_by_ack);\n"
      "  cover property (req_followed_by_ack);\n"
      "endchecker : req_ack_chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "req_ack_chk");
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 3u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kPropertyDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kCoverProperty));
}

// §3.6: Checker also encapsulates "modeling code" — variables, initial blocks,
//        always blocks used alongside assertions for auxiliary verification.
TEST(ParserClause03, Cl3_6_ModelingCodeInChecker) {
  auto r = ParseWithPreprocessor(
      "checker model_chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "  always @(flag) flag <= ~flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAlwaysBlock));
  EXPECT_GE(r.cu->checkers[0]->items.size(), 3u);  // var + initial + always
}

// =============================================================================
// LRM §3.8 — Subroutines
// =============================================================================
// §3.8: "A task is called as a statement. A task can have any number of
//        input, output, inout, and ref arguments, but does not return a
//        value. Tasks can block simulation time during execution."
TEST(ParserClause03, Cl3_8_TaskAllDirectionsAndBlocking) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  task my_task(input int a, output int b, inout int c, ref int d);\n"
      "    #10;\n"
      "    b = a + c;\n"
      "    c = d;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task = FindItemByKind(r, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  EXPECT_EQ(task->name, "my_task");
  ASSERT_EQ(task->func_args.size(), 4u);
  EXPECT_EQ(task->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(task->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(task->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(task->func_args[3].direction, Direction::kRef);
  // Task has a body with delay (#10 blocks time) + assignments
  EXPECT_GE(task->func_body_stmts.size(), 1u);
}

}  // namespace
