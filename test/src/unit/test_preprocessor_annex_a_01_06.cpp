#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(InterfaceItemsParsing, FunctionsAndTasks) {
  auto r = ParseWithPreprocessor(
      "interface ifc;\n"
      "  function automatic int get_data;\n"
      "    return 42;\n"
      "  endfunction\n"
      "  task automatic send(input int val);\n"
      "  endtask\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl));
}

TEST(InterfaceItemsParsing, IfdefSelectsInterfaceItem) {
  auto r = ParseWithPreprocessor(
      "`define HAS_MODPORT\n"
      "interface ifc;\n"
      "  logic data;\n"
      "`ifdef HAS_MODPORT\n"
      "  modport master(output data);\n"
      "`endif\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
}

TEST(InterfaceItemsParsing, IfndefOmitsInterfaceItem) {
  auto r = ParseWithPreprocessor(
      "`define HAS_MODPORT\n"
      "interface ifc;\n"
      "  logic data;\n"
      "`ifndef HAS_MODPORT\n"
      "  modport master(output data);\n"
      "`endif\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports.size(), 0u);
}

TEST(InterfaceItemsParsing, MacroExpandsToInterfaceItem) {
  auto r = ParseWithPreprocessor(
      "`define DECL_PORT(name) logic name\n"
      "interface ifc;\n"
      "  `DECL_PORT(data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
}

}  // namespace
