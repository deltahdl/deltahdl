#include <gtest/gtest.h>

#include "fixture_program.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST_F(DpiParseTest, DpiImportOpenArrayFormalAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f2(logic [127:0] i []);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  ASSERT_EQ(items[0]->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(items[0]->func_args[0].unpacked_dims[0], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportMultiDimensionOpenArrayFormalAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f3(input int i [][]);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  ASSERT_EQ(items[0]->func_args[0].unpacked_dims.size(), 2u);
  EXPECT_EQ(items[0]->func_args[0].unpacked_dims[0], nullptr);
  EXPECT_EQ(items[0]->func_args[0].unpacked_dims[1], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportSizedUnpackedFormalIsNotOpen) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void g(input int packet [1:10]);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  ASSERT_EQ(items[0]->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_NE(items[0]->func_args[0].unpacked_dims[0], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

}  // namespace
