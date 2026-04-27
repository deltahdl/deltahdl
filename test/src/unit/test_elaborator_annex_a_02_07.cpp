#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- task_declaration ---

TEST(TaskDeclElaboration, TaskDeclAddedToModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task my_task(input int x);\n"
      "    $display(\"%0d\", x);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->function_decls.size(), 1u);
  EXPECT_EQ(mod->function_decls[0]->kind, ModuleItemKind::kTaskDecl);
}

// Lifetime-keyword acceptance on task declarations is a §6.21 rule;
// the corresponding elaborator tests live in test_elaborator_clause_06_21.cpp.

// --- task_body_declaration ---

TEST(TaskDeclElaboration, TaskOldStylePortsElaborate) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  task my_task;\n"
      "    input int a;\n"
      "    output int b;\n"
      "    b = a + 1;\n"
      "  endtask\n"
      "endmodule\n"));
}

TEST(TaskDeclElaboration, TaskWithEndLabelElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  task my_task;\n"
      "  endtask : my_task\n"
      "endmodule\n"));
}

TEST(TaskDeclElaboration, TaskEmptyBodyElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  task empty_task;\n"
      "  endtask\n"
      "endmodule\n"));
}

// --- tf_port_list / tf_port_item ---

TEST(TaskDeclElaboration, TaskMultiplePortsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task my_task(input int a, output int b, inout int c);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  EXPECT_EQ(mod->function_decls[0]->func_args.size(), 3u);
}

TEST(TaskDeclElaboration, TaskPortDefaultValueElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  task my_task(input int x = 5);\n"
      "  endtask\n"
      "endmodule\n"));
}

// --- tf_port_direction ---

TEST(TaskDeclElaboration, TaskConstRefPortElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  task my_task(const ref int x);\n"
      "  endtask\n"
      "endmodule\n"));
}

// --- task_prototype ---

TEST(TaskDeclElaboration, TaskPrototypeExternElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  extern task my_task(input int x);\n"
      "endmodule\n"));
}

// --- multiple tasks ---

TEST(TaskDeclElaboration, MultipleTasksElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task t1; endtask\n"
      "  task t2; endtask\n"
      "  task t3; endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->function_decls.size(), 3u);
}

}  // namespace
