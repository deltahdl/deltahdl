// §23.2: Module definitions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.1.2 module_declaration — all forms
// =============================================================================
// module_keyword ::= module | macromodule
TEST(SourceText, ModuleKeywordMacromodule) {
  auto r = ParseWithPreprocessor("macromodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(ParserSection23, MacromoduleDefinition) {
  auto r = ParseWithPreprocessor(
      "macromodule top;\n"
      "  wire a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

}  // namespace
