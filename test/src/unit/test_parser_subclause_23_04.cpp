#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleAndHierarchyParsing, NestedModuleParsesOk) {
  EXPECT_TRUE(
      ParseOk("module outer;\n"
              "  wire w;\n"
              "  module inner;\n"
              "    assign w = 1'b1;\n"
              "  endmodule\n"
              "  inner i1();\n"
              "endmodule\n"));
}

TEST(ModuleAndHierarchyParsing, NestedModuleMultiple) {
  EXPECT_TRUE(
      ParseOk("module outer(input d, ck, output q, nq);\n"
              "  wire q1, nq1;\n"
              "  module ff1;\n"
              "    nand g1(nq1, d, q1);\n"
              "  endmodule\n"
              "  ff1 i1();\n"
              "  module ff2;\n"
              "    nand g2(q1, ck, nq1);\n"
              "  endmodule\n"
              "  ff2 i2();\n"
              "endmodule\n"));
}

TEST(ModuleAndHierarchyParsing, NestedInterfaceDecl) {
  auto r = Parse(
      "module outer;\n"
      "  interface inner_ifc;\n"
      "  endinterface\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

TEST(ModuleAndHierarchyParsing, NestedProgramDecl) {
  auto r = Parse(
      "module outer;\n"
      "  program inner_prg;\n"
      "  endprogram\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

TEST(ModuleAndHierarchyParsing, NestedCheckerDecl) {
  auto r = Parse(
      "module outer;\n"
      "  checker inner_chk;\n"
      "  endchecker\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

TEST(ModuleAndHierarchyParsing, NestedMacromoduleDecl) {
  auto r = Parse(
      "module outer;\n"
      "  macromodule inner_mac;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

TEST(ModuleAndHierarchyParsing, NestedModuleNamePreserved) {
  auto r = Parse(
      "module outer;\n"
      "  module my_inner;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nested = r.cu->modules[0]->items[0]->nested_module_decl;
  ASSERT_NE(nested, nullptr);
  EXPECT_EQ(nested->name, "my_inner");
}

TEST(ModuleAndHierarchyParsing, NestedModuleWithBodyItems) {
  auto r = Parse(
      "module outer;\n"
      "  module inner;\n"
      "    wire a;\n"
      "    logic b;\n"
      "    assign a = b;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nested = r.cu->modules[0]->items[0]->nested_module_decl;
  ASSERT_NE(nested, nullptr);
  EXPECT_GE(nested->items.size(), 3u);
}

TEST(ModuleAndHierarchyParsing, DeepNesting) {
  EXPECT_TRUE(
      ParseOk("module a;\n"
              "  module b;\n"
              "    module c;\n"
              "    endmodule\n"
              "  endmodule\n"
              "endmodule\n"));
}

TEST(ModuleAndHierarchyParsing, NestedModuleWithPorts) {
  auto r = Parse(
      "module outer;\n"
      "  module inner(input a, output b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nested = r.cu->modules[0]->items[0]->nested_module_decl;
  ASSERT_NE(nested, nullptr);
  EXPECT_FALSE(nested->ports.empty());
}

TEST(ModuleAndHierarchyParsing, NestedModulePortlessNoPorts) {
  auto r = Parse(
      "module outer;\n"
      "  module inner;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nested = r.cu->modules[0]->items[0]->nested_module_decl;
  ASSERT_NE(nested, nullptr);
  EXPECT_TRUE(nested->ports.empty());
}

// §23.4: a module declared inside another module may also be explicitly
// instantiated alongside its declaration (the form shown by the standard's
// nested flip-flop example). The parser must yield both the nested module
// declaration item and the instantiation item in the enclosing module's body.
TEST(ModuleAndHierarchyParsing, NestedModuleDeclaredAndInstantiated) {
  auto r = Parse(
      "module outer;\n"
      "  module inner;\n"
      "    wire w;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kNestedModuleDecl));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kModuleInst));
}

TEST(ModuleAndHierarchyParsing, ErrorNestedModuleMissingEndmodule) {
  auto r = Parse(
      "module outer;\n"
      "  module inner;\n"
      "    wire w;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
