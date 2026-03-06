#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §3.12: Compilation reads source and checks syntax/semantics.

TEST(ParserClause03, Cl3_12_CompilationProducesAST) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// §3.12: Elaboration binds module, program, interface, checker, and
// primitive instances.

TEST(ParserClause03, Cl3_12_AllDesignElementTypesCompile) {
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
}

// §3.12: Elaboration expands instantiations and computes parameter values.

TEST(ParserClause03, Cl3_12_ParameterOverrideCompiles) {
  auto r = Parse(
      "module sub #(parameter W = 8);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.W(16)) u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst));
}

// §3.12: Package compilation must precede references to it.

TEST(ParserClause03, Cl3_12_PackagePrecedesImport) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  byte_t data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl));
}

// §3.12: Compilation handles multiple design elements in order.

TEST(ParserClause03, Cl3_12_OrderOfDesignElements) {
  auto r = Parse(
      "package p; endpackage\n"
      "module a; endmodule\n"
      "module b; a u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
}

}  // namespace
