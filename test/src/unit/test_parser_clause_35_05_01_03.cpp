#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST_F(AnnexHParseTest, AnnexHDpiImportContext) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" context function void set_callback();\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "set_callback");
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_task);
}

// §35.5.1.3: an imported task can never be declared pure; the parser must
// reject the pure property on a task import declaration.
TEST_F(AnnexHParseTest, AnnexHDpiPureTaskRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" pure task t();\n"
      "endmodule\n");
  EXPECT_TRUE(diag_.HasErrors());
}

// §35.5.1.3: the pure property remains legal on an imported function, so a
// pure function import must parse without error.
TEST_F(AnnexHParseTest, AnnexHDpiPureFunctionAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function int f(input int a);\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_task);
}

// §35.5.1.3: the prohibition is specific to the pure property; an imported
// task may still carry context, so a context task must parse without error.
// This pins the rejection to pure rather than to task properties in general.
TEST_F(AnnexHParseTest, AnnexHDpiContextTaskAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" context task t();\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_task);
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_pure);
}

// §35.5.1.3: the pure-on-task rejection must still fire when an explicit
// c_identifier linkage name follows the property, which routes parsing through
// the separate c_identifier branch before the task keyword is seen.
TEST_F(AnnexHParseTest, AnnexHDpiPureTaskWithCIdentifierRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" pure c_do = task do_work();\n"
      "endmodule\n");
  EXPECT_TRUE(diag_.HasErrors());
}

}
