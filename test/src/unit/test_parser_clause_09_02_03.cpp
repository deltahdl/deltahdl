#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProcessTimingAndControlParsing, FinalBlockWithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  final begin\n"
      "    $display(\"cycles: %0d\", count);\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* final_item = FindItemByKind(r, ModuleItemKind::kFinalBlock);
  ASSERT_NE(final_item, nullptr);
  ASSERT_NE(final_item->body, nullptr);
  EXPECT_EQ(final_item->body->kind, StmtKind::kBlock);
  EXPECT_GE(final_item->body->stmts.size(), 2u);
}

TEST(ProcessTimingAndControlParsing, MultipleFinalBlocks) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"final1\");\n"
      "  final $display(\"final2\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST(SchedulingSemanticsParsing, ProgramWithFinalBlock) {
  auto r = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}
TEST(ProcessParsing, BlockInFinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final begin\n"
      "    $display(\"sim done\");\n"
      "    $display(\"cycles: %0d\", cnt);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
      EXPECT_EQ(item->body->kind, StmtKind::kBlock);
      EXPECT_GE(item->body->stmts.size(), 2u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ProceduralAssignAndControlParsing, StructuredProcFinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

TEST(SchedulingSemanticsParsing, FinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final begin\n"
      "    $display(\"simulation done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item->body, nullptr);
}

TEST(ProcessParsing, FinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(FinalBlock, DisplayCall) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

}  // namespace
