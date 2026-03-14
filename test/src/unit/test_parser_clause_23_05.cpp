#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ModuleAndHierarchyParsing, ExternModuleHeader) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "foo");
  EXPECT_TRUE(mod->is_extern);
  EXPECT_TRUE(mod->items.empty());
}

TEST(ModuleAndHierarchyParsing, ExternModulePorts) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  VerifyTwoPortModule(r, "a", Direction::kInput, "b", Direction::kOutput);
}

TEST(ModuleAndHierarchyParsing, ExternModuleNoBody) {
  auto r = Parse(
      "extern module bar(input logic x);\n"
      "module baz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2);
  struct Expected {
    const char* name;
    bool is_extern;
  };
  Expected expected[] = {{"bar", true}, {"baz", false}};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(r.cu->modules[i]->name, expected[i].name);
    EXPECT_EQ(r.cu->modules[i]->is_extern, expected[i].is_extern);
  }
}

TEST(ModuleAndHierarchyParsing, ExternModuleNonAnsiPorts) {
  auto r = Parse("extern module m (a, b, c);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  EXPECT_TRUE(mod->is_extern);
  EXPECT_TRUE(mod->items.empty());
}

TEST(ModuleAndHierarchyParsing, ExternModuleWithParams) {
  auto r = Parse(
      "extern module a #(parameter size = 8)\n"
      "  (input [size:0] x, output logic y);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "a");
  EXPECT_TRUE(mod->is_extern);
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "size");
  ASSERT_EQ(mod->ports.size(), 2);
}

TEST(ModuleAndHierarchyParsing, ExternModuleFollowedByDefinition) {
  auto r = Parse(
      "extern module ext (input a, output b);\n"
      "module other (input x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2);
  EXPECT_EQ(r.cu->modules[0]->name, "ext");
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_EQ(r.cu->modules[1]->name, "other");
  EXPECT_FALSE(r.cu->modules[1]->is_extern);
}

}  // namespace
