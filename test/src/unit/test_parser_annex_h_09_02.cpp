#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

void ExpectImportAndExport(const std::vector<ModuleItem*>& items) {
  const ModuleItem* imp = FindItemByKind(items, ModuleItemKind::kDpiImport);
  ASSERT_NE(imp, nullptr);
  EXPECT_EQ(imp->name, "f");
  const ModuleItem* exp = FindItemByKind(items, ModuleItemKind::kDpiExport);
  ASSERT_NE(exp, nullptr);
  EXPECT_EQ(exp->name, "g");
}

constexpr const char* kImportAndExport =
    "  import \"DPI-C\" context function void f();\n"
    "  function void g(); endfunction\n"
    "  export \"DPI-C\" function g;\n";

TEST(DpiDeclarativeScopeParsing, AModuleDeclaresAnImportAndAnExport) {
  auto r = Parse(std::string("module m;\n") + kImportAndExport + "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ExpectImportAndExport(r.cu->modules[0]->items);
}

TEST(DpiDeclarativeScopeParsing, AProgramDeclaresAnImportAndAnExport) {
  auto r =
      Parse(std::string("program p;\n") + kImportAndExport + "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ExpectImportAndExport(r.cu->programs[0]->items);
}

TEST(DpiDeclarativeScopeParsing, AnInterfaceDeclaresAnImportAndAnExport) {
  auto r = Parse(std::string("interface i;\n") + kImportAndExport +
                 "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ExpectImportAndExport(r.cu->interfaces[0]->items);
}

TEST(DpiDeclarativeScopeParsing, APackageDeclaresAnImportAndAnExport) {
  auto r =
      Parse(std::string("package pkg;\n") + kImportAndExport + "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ExpectImportAndExport(r.cu->packages[0]->items);
}

TEST(DpiDeclarativeScopeParsing,
     TheCompilationUnitDeclaresAnImportAndAnExport) {
  auto r = Parse(kImportAndExport);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ExpectImportAndExport(r.cu->cu_items);
}

TEST(DpiDeclarativeScopeParsing, AGenerateBlockDeclaresAnImportAndAnExport) {
  auto r = Parse(std::string("module m;\n"
                             "  if (1) begin : blk\n") +
                 kImportAndExport +
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const ModuleItem* gen =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen, nullptr);
  EXPECT_EQ(FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiImport),
            nullptr);
  ExpectImportAndExport(gen->gen_body);
}

TEST(DpiDeclarativeScopeParsing,
     ALoopGenerateBlockDeclaresAnImportAndAnExport) {
  auto r = Parse(std::string("module m;\n"
                             "  for (genvar i = 0; i < 2; i++) begin : blk\n") +
                 kImportAndExport +
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* gen =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  ExpectImportAndExport(gen->gen_body);
}

TEST(DpiDeclarativeScopeParsing,
     ACaseGenerateBlockDeclaresAnImportAndAnExport) {
  auto r = Parse(std::string("module m;\n"
                             "  case (1)\n"
                             "  1: begin : blk\n") +
                 kImportAndExport +
                 "  end\n"
                 "  endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* gen =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateCase);
  ASSERT_NE(gen, nullptr);
  ASSERT_EQ(gen->gen_case_items.size(), 1u);
  ExpectImportAndExport(gen->gen_case_items[0].body);
}

TEST(DpiDeclarativeScopeParsing, AClassDeclaresNoImportAndNoExport) {
  auto imported = Parse(
      "class C;\n"
      "  import \"DPI-C\" context function void f();\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(imported.diags,
                            "DPI import declaration is not allowed in class "
                            "scope",
                            2, "35.5.4"));
  auto exported = Parse(
      "class C;\n"
      "  function void g(); endfunction\n"
      "  export \"DPI-C\" function g;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(exported.diags,
                            "DPI export declaration is not allowed in class "
                            "scope",
                            3, "35.7"));
}

TEST(DpiDeclarativeScopeParsing, ACheckerDeclaresNoImportAndNoExport) {
  auto imported = Parse(
      "checker c;\n"
      "  import \"DPI-C\" context function void f();\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(imported.diags,
                            "a DPI import declaration is not an item of a "
                            "checker",
                            2, "A.1.8"));
  auto exported = Parse(
      "checker c;\n"
      "  function void g(); endfunction\n"
      "  export \"DPI-C\" function g;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(exported.diags,
                            "a DPI export declaration is not an item of a "
                            "checker",
                            3, "A.1.8"));
}

TEST(DpiDeclarativeScopeParsing, DISABLED_AFunctionBodyDeclaresNoImport) {
  auto r = Parse(
      "module m;\n"
      "  function int h();\n"
      "    import \"DPI-C\" context function void f();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "DPI import declaration", 3, "35.5.4"));
}

TEST(DpiDeclarativeScopeParsing, DISABLED_ATaskBodyDeclaresNoImport) {
  auto r = Parse(
      "module m;\n"
      "  task h();\n"
      "    import \"DPI-C\" context function void f();\n"
      "  endtask\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "DPI import declaration", 3, "35.5.4"));
}

}  // namespace
