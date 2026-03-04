#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserA602, FinalConstruct_SingleStmt) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserA602, FinalConstruct_BeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  final begin\n"
      "    $display(\"test1\");\n"
      "    $display(\"test2\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ParserA602, FinalConstruct_Multiple) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"a\");\n"
      "  final $display(\"b\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto finals = FindItems(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  EXPECT_EQ(finals.size(), 2u);
}

TEST(ParserA602, Integration_InitialFinalCoexistence) {

  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"start\");\n"
      "    a = 0;\n"
      "  end\n"
      "  final begin\n"
      "    $display(\"end\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* init = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  auto* fin = FindItem(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(fin, nullptr);
}

TEST(ParserSection9c, FinalBlockWithBeginEnd) {
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

TEST(ParserSection9c, MultipleFinalBlocks) {
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

TEST(ParserSection4, Sec4_6_ProgramWithFinalBlock) {
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
TEST(ParserSection9, Sec9_3_1_BlockInFinalBlock) {
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

TEST_F(ProgramTestParse, ProgramWithFinalBlock) {
  auto* unit = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}
TEST(ParserSection9b, StructuredProcFinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

TEST(ParserSection4, Sec4_5_FinalBlock) {
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

TEST(ParserSection9, FinalBlock) {
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

}
