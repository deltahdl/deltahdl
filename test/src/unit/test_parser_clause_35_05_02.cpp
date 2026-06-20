#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §35.5.2's restrictions on pure imports cannot be enforced unless the
// parser surfaces the pure marker on the import. This test observes the
// parser-stage precondition of that enforcement chain: a pure DPI import
// is recognized as such, recorded with dpi_is_pure set, and distinguished
// from context / task forms.
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
