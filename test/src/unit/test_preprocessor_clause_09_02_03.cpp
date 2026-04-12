#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(FinalProcedurePreprocessing, MacroExpandsInsideFinalBlock) {
  auto r = ParseWithPreprocessor(
      "`define MSG \"done\"\n"
      "module m;\n"
      "  final $display(`MSG);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(FinalProcedurePreprocessing, MacroExpandsToFinalBody) {
  auto r = ParseWithPreprocessor(
      "`define FINAL_BODY x = 1\n"
      "module m;\n"
      "  logic [31:0] x;\n"
      "  final `FINAL_BODY;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(FinalProcedurePreprocessing, ConditionalCompilationAroundFinal) {
  auto r = ParseWithPreprocessor(
      "`define HAS_FINAL\n"
      "module m;\n"
      "`ifdef HAS_FINAL\n"
      "  final $display(\"done\");\n"
      "`endif\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(FinalProcedurePreprocessing, ConditionalCompilationOmitsFinal) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "`ifdef HAS_FINAL\n"
      "  final $display(\"done\");\n"
      "`endif\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    EXPECT_NE(item->kind, ModuleItemKind::kFinalBlock);
  }
}

}  // namespace
