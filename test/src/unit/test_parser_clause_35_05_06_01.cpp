#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// §35.5.6.1: a formal argument of an imported function is an *open array* when a
// range of one or more of its dimensions is left unspecified, denoted with
// empty square brackets "[]". Imported functions are explicitly permitted to
// take such formals, so this LRM example import parses without error and the
// open dimension is recorded as a dimension with no bounds.
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
  // The unsized unpacked dimension "[]" is the open-array marker: one
  // dimension entry with no bounds expression.
  ASSERT_EQ(items[0]->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(items[0]->func_args[0].unpacked_dims[0], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

// §35.5.6.1: "The number of unpacked dimensions is not restricted." A formal can
// be an open array in several unpacked dimensions at once -- each unsized
// dimension is a separate unbounded entry -- and the import still parses
// cleanly, matching the LRM's two-dimensional open-array example shape.
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

// §35.5.6.1: a formal is an open array only when a dimension is left
// *unspecified*. A sized unpacked dimension is not an open dimension, so its
// bounds are recorded -- confirming the open-array property keys on the empty
// "[]" form and not on the mere presence of an unpacked dimension.
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
