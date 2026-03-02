// §23.5: Extern modules

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.1.2 module_declaration — wildcard port form: module m (.*);
// =============================================================================
TEST(SourceText, ModuleWildcardPorts) {
  auto r = ParseWithPreprocessor("module m(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->has_wildcard_ports);
}

// Extern module declaration.
TEST(SourceText, ExternModule) {
  auto r = ParseWithPreprocessor("extern module m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

}  // namespace
