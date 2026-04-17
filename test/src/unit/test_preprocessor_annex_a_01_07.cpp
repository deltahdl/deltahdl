#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ProgramItemsParsing, IfdefSelectsProgramItem) {
  auto r = ParseWithPreprocessor(
      "`define HAS_INIT\n"
      "program p;\n"
      "`ifdef HAS_INIT\n"
      "  initial $display(\"yes\");\n"
      "`endif\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(ProgramItemsParsing, IfndefOmitsProgramItem) {
  auto r = ParseWithPreprocessor(
      "`define HAS_FINAL\n"
      "program p;\n"
      "`ifndef HAS_FINAL\n"
      "  final $display(\"no\");\n"
      "`endif\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFinalBlock));
}

TEST(ProgramItemsParsing, MacroExpandsToProgramItem) {
  auto r = ParseWithPreprocessor(
      "`define PROG_BODY initial $display(\"macro\");\n"
      "program p;\n"
      "  `PROG_BODY\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

}  // namespace
