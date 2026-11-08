#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(PureDpiImportParsing, ParserMarksPureFlagOnImport) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function real sin_approx(real x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "sin_approx");
  EXPECT_TRUE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_task);
}

}  // namespace
