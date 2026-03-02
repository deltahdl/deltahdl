// Annex A.1.2: SystemVerilog source text

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.1.2 description — all alternatives
// =============================================================================
// description: module_declaration
TEST(SourceText, DescriptionModule) {
  auto r = ParseWithPreprocessor("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// Multiple descriptions in source text.
TEST(SourceText, MultipleDescriptions) {
  auto r = ParseWithPreprocessor(
      "module m1; endmodule\n"
      "interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

}  // namespace
