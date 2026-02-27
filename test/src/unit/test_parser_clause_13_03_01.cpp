// §13.3.1: Static and automatic tasks

#include "fixture_parser.h"

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

};

// =============================================================================
// A.2.7 Task declarations
// =============================================================================
// ---------------------------------------------------------------------------
// task_declaration ::=
//   task [ dynamic_override_specifiers ] [ lifetime ] task_body_declaration
// ---------------------------------------------------------------------------
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

}  // namespace
