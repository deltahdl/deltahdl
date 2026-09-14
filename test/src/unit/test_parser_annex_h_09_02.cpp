#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §H.9.2: DPI imported and exported tasks and functions can be declared in a
// module, program, interface, package, compilation-unit scope or generate
// declarative scope. Each scope below declares an import and an export, and
// the parser accepts the pair where the clause allows it.

// The items of a scope carry one import and one export.
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

// The compilation-unit scope: the declarations stand outside every module,
// and the export is what the parser did not read there before this clause.
TEST(DpiDeclarativeScopeParsing,
     TheCompilationUnitDeclaresAnImportAndAnExport) {
  auto r = Parse(kImportAndExport);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ExpectImportAndExport(r.cu->cu_items);
}

// A generate declarative scope: the pair stands in a generate block of a
// module, under the block's own items rather than the module's.
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

}  // namespace
