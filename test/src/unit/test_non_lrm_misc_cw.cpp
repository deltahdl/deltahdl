// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// Verify import/export flags are mutually exclusive in AST
TEST(ParserA29, ImportFlag_NotExport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_FALSE(mp->ports[0].is_export);
}

// Verify function prototype return type stored
TEST(ParserA29, FunctionPrototype_ReturnType) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import function int compute(input int a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mp->ports[0].prototype->data_type.kind, DataTypeKind::kInt);
}

// Verify task prototype with arguments stores them
TEST(ParserA29, TaskPrototype_HasArgs) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import task Read(input logic [7:0] raddr));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_FALSE(mp->ports[0].prototype->func_args.empty());
}

// =============================================================================
// LRM section 26.2 -- Package declarations
// =============================================================================
TEST(ParserSection26, EmptyPackage) {
  auto r = Parse(
      "package pkg;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(ParserSection26, PackageWithEndLabel) {
  auto r = Parse(
      "package my_pkg;\n"
      "endpackage : my_pkg\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "my_pkg");
}

TEST(ParserSection26, PackageWithTypedef) {
  auto r = Parse(
      "package types_pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_FALSE(r.cu->packages[0]->items.empty());
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

}  // namespace
