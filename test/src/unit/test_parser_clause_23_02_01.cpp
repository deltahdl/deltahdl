// §23.2.1: Module header definition

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// 27. Module with static lifetime qualifier
// =============================================================================
TEST(ParserSection4, Sec4_9_3_StaticModuleLifetime) {
  EXPECT_TRUE(
      ParseOk("module static m;\n"
              "  function int fn();\n"
              "    return 0;\n"
              "  endfunction\n"
              "endmodule\n"));
}

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// --- End labels on design elements (LRM section 3) ---
TEST(ParserSection23, EndLabelModule) {
  auto r = Parse("module foo; endmodule : foo\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

TEST(ParserSection23, EndLabelModuleNoLabel) {
  auto r = Parse("module bar; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
}

// --- Package import in module headers (LRM section 26.4) ---
TEST(ParserSection23, ModuleHeaderImport) {
  auto r = Parse(
      "module m import pkg::*; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  // The header import generates an import item in the module body.
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
}

}  // namespace
