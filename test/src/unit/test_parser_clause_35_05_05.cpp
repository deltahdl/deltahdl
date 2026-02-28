// §35.5.5: Function result

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;
}
;

namespace {

TEST(ParserA26, DpiImportFunctionVoid) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void c_print(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

}  // namespace
