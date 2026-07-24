#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ExternModuleParsing, ExternModuleHeader) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "foo");
  EXPECT_TRUE(mod->is_extern);
  EXPECT_TRUE(mod->items.empty());
}

TEST(ExternModuleParsing, ExternModulePorts) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  VerifyTwoPortModule(r, "a", Direction::kInput, "b", Direction::kOutput);
}

TEST(ExternModuleParsing, ExternModuleNonAnsiPorts) {
  auto r = Parse("extern module m (a, b, c);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  EXPECT_TRUE(mod->is_extern);
  EXPECT_TRUE(mod->items.empty());
}

TEST(ExternModuleParsing, ExternModuleWithParams) {
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

TEST(ExternModuleParsing, ExternMacromodule) {
  auto r = Parse("extern macromodule m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

TEST(ExternModuleParsing, ExternWithLifetime) {
  auto r = Parse("extern module automatic m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_TRUE(r.cu->modules[0]->is_automatic);
}

TEST(ExternModuleParsing, ExternAnsiEmptyPortList) {
  auto r = Parse("extern module m();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ExternModuleParsing, ExternAnsiWithAttributes) {
  auto r = Parse("(* keep *) extern module m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_FALSE(r.cu->modules[0]->attrs.empty());
}

TEST(ExternModuleParsing, ExternStaticLifetime) {
  auto r = Parse("extern module static m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_FALSE(r.cu->modules[0]->is_automatic);
}

TEST(ExternModuleParsing, MultipleExternDeclarations) {
  auto r = Parse(
      "extern module m (a, b, c, d);\n"
      "extern module a #(parameter size = 8, parameter type TP = logic [7:0])\n"
      "  (input [size:0] x, output TP y);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_EQ(r.cu->modules[1]->name, "a");
  EXPECT_TRUE(r.cu->modules[1]->is_extern);
}

TEST(ExternModuleParsing, ExternWithTypeParameter) {
  auto r = Parse(
      "extern module a #(parameter size = 8, parameter type TP = logic [7:0])\n"
      "  (input [size:0] x, output TP y);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->is_extern);
  ASSERT_EQ(mod->params.size(), 2u);
  EXPECT_EQ(mod->params[0].first, "size");
  EXPECT_EQ(mod->params[1].first, "TP");
}

TEST(ExternModuleParsing, ExternAndSameNameDefinition) {
  auto r = Parse(
      "extern module m(input a, output b);\n"
      "module m(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_EQ(r.cu->modules[1]->name, "m");
  EXPECT_FALSE(r.cu->modules[1]->is_extern);
}

// §23.5: an extern module declaration can appear at any level of the
// instantiation hierarchy, including nested inside a module body. The parser
// stores it as a nested module declaration flagged is_extern.
TEST(ExternModuleParsing, NestedExternModuleDecl) {
  auto r = Parse(
      "module top;\n"
      "  extern module child(input logic a, output logic b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* top = r.cu->modules[0];
  const ModuleDecl* nested = nullptr;
  for (auto* item : top->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl) {
      nested = item->nested_module_decl;
    }
  }
  ASSERT_NE(nested, nullptr);
  EXPECT_EQ(nested->name, "child");
  EXPECT_TRUE(nested->is_extern);
  ASSERT_EQ(nested->ports.size(), 2u);
}

TEST(ExternModuleParsing, ErrorMissingSemicolon) {
  EXPECT_FALSE(ParseOk("extern module m(input a)\n"));
}

TEST(ExternModuleParsing, ErrorMissingModuleName) {
  EXPECT_FALSE(ParseOk("extern module ;\n"));
}

}  // namespace
