#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(ModuleDeclarations, MacromoduleKeywordIntroducesModule) {
  auto r = Parse("macromodule mm; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
  EXPECT_EQ(r.cu->modules[0]->name, "mm");
}

TEST(ModuleDeclarations, ModuleNameMatchesIdentifier) {
  auto r = Parse("module my_design; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "my_design");
}

TEST(ModuleDeclarations, ModuleKeywordWithoutNameIsRejected) {
  auto r = Parse("module ; endmodule");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 1, "23.2.1"));
}

TEST(ModuleDeclarations, MacromoduleKeywordWithoutNameIsRejected) {
  auto r = Parse("macromodule ; endmodule");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 1, "23.2.1"));
}

TEST(ModuleDefinitions, ModuleWithoutEndmoduleIsRejected) {
  auto r = Parse("module m;");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endmodule', got EOF", 1, "23.2"));
}

TEST(ModuleDefinitions, MacromoduleWithoutEndmoduleIsRejected) {
  auto r = Parse("macromodule m;");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endmodule', got EOF", 1, "23.2"));
}

TEST(ModuleDefinitions, MultipleModulesInSource) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
}

bool ReportedUnderModuleDefinitionsAt(const std::string& src, uint32_t line) {
  auto r = Parse(src);
  const std::vector<Diagnostic>& diags = r.diags;
  for (const auto& d : diags) {
    if (d.severity == DiagSeverity::kError && d.loc.line == line &&
        d.subclause == "23.2") {
      return true;
    }
  }
  return false;
}

TEST(ModuleBracketing, DISABLED_AnotherEndKeywordDoesNotCloseAModule) {
  for (const char* closer : {"endinterface", "endprogram", "endchecker",
                             "endpackage", "endprimitive", "endconfig"}) {
    EXPECT_TRUE(ReportedUnderModuleDefinitionsAt(
        std::string("module m;\n") + closer + "\n", 2))
        << closer;
  }
  EXPECT_TRUE(
      ReportedUnderModuleDefinitionsAt("macromodule m;\nendprogram\n", 2));
  EXPECT_TRUE(ReportedUnderModuleDefinitionsAt(
      "module o;\nmodule i;\nendinterface\nendmodule\n", 3));
}

TEST(ModuleBracketing, EndmoduleClosesTheModuleAndTheNestedModule) {
  EXPECT_FALSE(Parse("module m;\nendmodule\n").has_errors);
  EXPECT_FALSE(Parse("macromodule m;\nendmodule\n").has_errors);
  EXPECT_FALSE(
      Parse("module o;\nmodule i;\nendmodule\nendmodule\n").has_errors);
}

TEST(ModuleBracketing, DISABLED_AnEndmoduleClosingNoModuleIsReported) {
  EXPECT_TRUE(
      ReportedUnderModuleDefinitionsAt("module m;\nendmodule\nendmodule\n", 3));
  EXPECT_TRUE(ReportedUnderModuleDefinitionsAt(
      "interface i;\nendmodule\nendinterface\n", 2));
  EXPECT_TRUE(ReportedUnderModuleDefinitionsAt(
      "program p;\nendmodule\nendprogram\n", 2));
}

TEST(ModuleBracketing, OtherElementsCloseWithTheirOwnEndKeyword) {
  EXPECT_FALSE(Parse("interface i;\nendinterface\n").has_errors);
  EXPECT_FALSE(Parse("program p;\nendprogram\n").has_errors);
}

struct RefusedHost {
  const char* opener;
  const char* closer;
  const char* message;
  const char* subclause;
};

TEST(MacromoduleDefinitions, RefusedWhereverAModuleIsRefused) {
  for (const auto& h : {
           RefusedHost{"program p;\n", "endprogram\n",
                       "module declarations not allowed in programs", "24.3"},
           RefusedHost{"package k;\n", "endpackage\n",
                       "a module, interface or program declaration is not an "
                       "item of a package",
                       "A.1.11"},
       }) {
    for (const char* keyword : {"module", "macromodule"}) {
      auto r = Parse(std::string(h.opener) + keyword + " m; endmodule\n" +
                     h.closer + "module t; endmodule\n");
      EXPECT_TRUE(ReportedError(r.diags, h.message, 2, h.subclause))
          << keyword << " in " << h.opener;
    }
  }
  for (const char* keyword : {"module", "macromodule"}) {
    auto r = Parse(std::string("class c;\n") + keyword +
                   " m; endmodule\nendclass\nmodule t; endmodule\n");
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + keyword + "'", 2,
        "8.5"))
        << keyword;
  }
}

}  // namespace
