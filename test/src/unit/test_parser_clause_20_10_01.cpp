#include "builders_ast.h"
#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(SourceText, ElabSeverityFatal) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(1, \"assertion failed\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kElabSystemTask);
}

TEST(SourceText, ElabSeverityAllForms) {
  auto r = Parse(
      "module m;\n"
      "  $fatal;\n"
      "  $error(\"err\");\n"
      "  $warning(\"warn\");\n"
      "  $info;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 4u);
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(r.cu->modules[0]->items[i]->kind,
              ModuleItemKind::kElabSystemTask);
  }
}

bool HasItemKind(const std::vector<ModuleItem*>& items, ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(SourceText, ProgramElabSeverityTask) {
  auto r = Parse(
      "program prg;\n"
      "  $info(\"program loaded\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kElabSystemTask));
}

}
