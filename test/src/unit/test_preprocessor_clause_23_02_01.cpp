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

// Module with lifetime qualifier: module automatic m;
TEST(SourceText, ModuleWithLifetime) {
  auto r = ParseWithPreprocessor("module automatic m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// Module with end label: endmodule : m
TEST(SourceText, ModuleEndLabel) {
  auto r = ParseWithPreprocessor("module m; endmodule : m\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// =============================================================================
// A.1.3 Module parameters and ports
// =============================================================================
// parameter_port_list ::= #( )
TEST(SourceText, EmptyParameterPortList) {
  auto r = ParseWithPreprocessor("module m #(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->params.empty());
}

TEST(Parser, EmptyModule) {
  auto r = ParseWithPreprocessor("module empty; endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "empty");
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

}  // namespace
