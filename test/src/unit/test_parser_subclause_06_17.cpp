#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;
namespace {

TEST(DataTypeParsing, EventVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  event done;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "done");
}

TEST(DataTypeParsing, EventNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kEvent));
}

TEST(DataTypeParsing, EventAssignNull) {
  auto r = Parse(
      "module t;\n"
      "  event empty = null;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
}

TEST(DataTypeParsing, EventInitFromAnotherEvent) {
  auto r = Parse(
      "module t;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2u);
  auto* aliased = mod->items[1];
  EXPECT_EQ(aliased->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(aliased->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(aliased->name, "done_too");
  ASSERT_NE(aliased->init_expr, nullptr);
  EXPECT_EQ(aliased->init_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(aliased->init_expr->text, "done");
}

// A.2.2.1 gives data_type the bare alternative `event`, so an event
// declaration is a data_declaration, and A.2.8's block_item_declaration carries
// a data_declaration wherever A.6.3's seq_block and par_block put one. Neither
// §6.17 nor §15.5 narrows that: §6.17's own example is `event done;` with no
// enclosing scope stated.
//
// The declaration was read as an expression statement instead, so the event was
// never declared and every later reference to the name resolved to whatever
// else it happened to mean. Declaring one at module scope reaches the parser by
// another path and cannot fail this.

TEST(DataTypeParsing, EventDeclaredInASequentialBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    event done;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = FirstInitialStmt(r);
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->kind, StmtKind::kVarDecl);
  EXPECT_EQ(first->var_decl_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(first->var_name, "done");
}

// A.6.3 gives par_block the same block_item_declaration position, and §15.5's
// synchronization between two arms of a fork is what an event declared in a
// procedural block is for.
TEST(DataTypeParsing, EventDeclaredInAParallelBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial fork\n"
      "    event done;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fork_stmt = FirstInitialStmt(r);
  ASSERT_NE(fork_stmt, nullptr);
  ASSERT_EQ(fork_stmt->kind, StmtKind::kFork);
  ASSERT_FALSE(fork_stmt->fork_stmts.empty());
  EXPECT_EQ(fork_stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(fork_stmt->fork_stmts[0]->var_decl_type.kind, DataTypeKind::kEvent);
}

// A.2.7's tf_item_declaration carries a block_item_declaration into a task
// body, which is a third position the same check answers for.
TEST(DataTypeParsing, EventDeclaredInATaskBody) {
  auto r = Parse(
      "module t;\n"
      "  task go;\n"
      "    event done;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[0]->var_decl_type.kind, DataTypeKind::kEvent);
}

}  // namespace
