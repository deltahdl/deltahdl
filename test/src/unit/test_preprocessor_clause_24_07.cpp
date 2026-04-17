#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ProgramControlTasksPreprocessing, ExitPreservedInProgramInitial) {
  auto r = ParseWithPreprocessor(
      "program p;\n"
      "  initial $exit();\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(ProgramControlTasksPreprocessing, ExitInsideMacroExpansion) {
  auto r = ParseWithPreprocessor(
      "`define TERMINATE $exit()\n"
      "program p;\n"
      "  initial `TERMINATE;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

}  // namespace
