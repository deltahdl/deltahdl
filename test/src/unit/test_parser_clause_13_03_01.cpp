#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2TaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task automatic drive(input logic [7:0] val);\n"
      "    data = val;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(item->name, "drive");
}

TEST(ParserA27, TaskLifetimeAutomatic) {
  auto r = Parse(
      "module m;\n"
      "  task automatic my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(ParserA27, TaskLifetimeStatic) {
  auto r = Parse(
      "module m;\n"
      "  task static my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserA27, TaskLifetimeDefault) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(ParserSection4, Sec4_9_3_AutomaticTaskWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  task automatic delayed_write(input int val);\n"
      "    #10;\n"
      "    $display(\"val=%0d\", val);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kDelay);
}

TEST(ParserSection4, Sec4_9_3_AutoTaskWithEventControl) {
  auto r = Parse(
      "module m;\n"
      "  task automatic wait_clk(input logic clk);\n"
      "    @(posedge clk);\n"
      "    $display(\"clock edge\");\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kEventControl);
  ASSERT_FALSE(item->func_body_stmts[0]->events.empty());
  EXPECT_EQ(item->func_body_stmts[0]->events[0].edge, Edge::kPosedge);
}

TEST(ParserSection4, Sec4_9_3_TaskNoLifetimeQualifier) {
  auto r = Parse(
      "module m;\n"
      "  task plain_task();\n"
      "    $display(\"hello\");\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(ParserSection4, Sec4_9_3_AutomaticTaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task automatic do_work(input int n);\n"
      "    $display(\"work %0d\", n);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
  EXPECT_EQ(item->name, "do_work");
}

TEST(ParserSection4, Sec4_9_3_StaticTaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task static wait_cycles(input int n);\n"
      "    repeat (n) #1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_static);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_EQ(item->name, "wait_cycles");
}

static ModuleItem* FindFunc(ParseResult& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl &&
        item->kind != ModuleItemKind::kTaskDecl) {
      continue;
    }
    if (item->name == name) return item;
  }
  return nullptr;
}

TEST(ParserSection13, StaticTask) {
  auto r = Parse(
      "module m;\n"
      "  task static do_stuff();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "do_stuff");
  ASSERT_NE(tk, nullptr);
  EXPECT_TRUE(tk->is_static);
  EXPECT_FALSE(tk->is_automatic);
}

TEST(ParserSection6, AutomaticTaskDecl) {
  auto r = Parse(
      "module t;\n"
      "  task automatic my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserSection6, StaticTaskDecl) {
  auto r = Parse(
      "module t;\n"
      "  task static my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_static);
}

static ModuleItem* FirstFuncOrTask(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl)
      return item;
  }
  return nullptr;
}

TEST(ParserSection4, Sec4_9_4_StaticTaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task static log_event(input int code);\n"
      "    $display(\"event: %0d\", code);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* t = FirstFuncOrTask(r);
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(t->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(t->is_static);
  EXPECT_FALSE(t->is_automatic);
  EXPECT_EQ(t->name, "log_event");
}

TEST(ParserSection4, Sec4_9_4_AutoTaskWithVariousTypes) {
  auto r = Parse(
      "module m;\n"
      "  task automatic process();\n"
      "    int i_val;\n"
      "    logic [3:0] l_val;\n"
      "    real r_val;\n"
      "    i_val = 1;\n"
      "    l_val = 4'hA;\n"
      "    r_val = 3.14;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* t = FirstFuncOrTask(r);
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(t->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(t->is_automatic);
  EXPECT_EQ(t->name, "process");

  ASSERT_GE(t->func_body_stmts.size(), 3u);
  EXPECT_EQ(t->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(t->func_body_stmts[0]->var_decl_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(t->func_body_stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(t->func_body_stmts[1]->var_decl_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(t->func_body_stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(t->func_body_stmts[2]->var_decl_type.kind, DataTypeKind::kReal);
}

TEST(ParserSection4, Sec4_9_4_AutoTaskExplicitAutoLocals) {
  auto r = Parse(
      "module m;\n"
      "  task automatic run(input int seed);\n"
      "    automatic int local_seed = seed;\n"
      "    $display(local_seed);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* t = FirstFuncOrTask(r);
  ASSERT_NE(t, nullptr);
  EXPECT_TRUE(t->is_automatic);
  ASSERT_GE(t->func_body_stmts.size(), 1u);
  EXPECT_EQ(t->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(t->func_body_stmts[0]->var_is_automatic);
  EXPECT_EQ(t->func_body_stmts[0]->var_name, "local_seed");
  EXPECT_NE(t->func_body_stmts[0]->var_init, nullptr);
}

}  // namespace
