#include <gtest/gtest.h>

#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(AnnexHParseTest, DpiPureTaskRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" pure task t();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "an imported task cannot be declared pure", 2,
                            "35.5.4"));
}

TEST_F(AnnexHParseTest, DpiPureFunctionAccepted) {
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

TEST_F(AnnexHParseTest, DpiContextTaskAccepted) {
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

TEST_F(AnnexHParseTest, DpiImportWithoutAPropertyDeclaresNeither) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int f(input int a);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_FALSE(items[0]->dpi_is_pure || items[0]->dpi_is_context);
}

TEST_F(AnnexHParseTest, DpiPureTaskWithCIdentifierRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" pure c_do = task do_work();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "an imported task cannot be declared pure", 2,
                            "35.5.4"));
}

TEST_F(AnnexHParseTest, DpiPureContextTaskRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" pure context task t();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "an imported task cannot be declared pure", 2,
                            "35.5.4"));
}

}  // namespace
