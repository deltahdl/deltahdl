#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TaskDeclParsing, AutomaticTaskWithoutParens) {
  auto r = Parse(
      "module m;\n"
      "  task automatic my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(TaskDeclParsing, StaticTaskWithoutParens) {
  auto r = Parse(
      "module m;\n"
      "  task static my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_static);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(TaskLifetimeParsing, AutomaticTaskDecl) {
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

TEST(TaskLifetimeParsing, StaticTaskDeclWithRepeatDelay) {
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

}  // namespace
