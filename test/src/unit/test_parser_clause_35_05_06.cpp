// §35.5.6: Types of formal arguments

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Annex H - DPI import with bit/logic vector arguments
// =============================================================================
TEST_F(AnnexHParseTest, AnnexHDpiImportBitLogicArgs) {
  // DPI functions can take bit and logic vector arguments corresponding to
  // SvBitVecVal and SvLogicVecVal on the C side.
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void send_bits(\n"
      "    input bit [31:0] data,\n"
      "    input logic [7:0] ctrl\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[0]->func_args.size(), 2u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(items[0]->func_args[0].name, "data");
  EXPECT_EQ(items[0]->func_args[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[0]->func_args[1].name, "ctrl");
}

}  // namespace
