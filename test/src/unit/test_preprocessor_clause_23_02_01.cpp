// §23.2.1: Module header definition

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, ModuleWithoutBeginKeywords) {
  auto r = ParseWithPreprocessor(
      "module m1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m1");
}

// =============================================================================
// LRM §3.3 — Modules
// =============================================================================
// §3.3 Module with end label
TEST(ParserClause03, Cl3_3_ModuleEndLabel) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "endmodule : m\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

}  // namespace
