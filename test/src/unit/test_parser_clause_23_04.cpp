// §23.4: Nested modules

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// Nested module_declaration as non_port_module_item.
TEST(SourceText, NestedModuleDeclaration) {
  auto r = Parse(
      "module outer;\n"
      "  module inner;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->nested_module_decl, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items[0]->nested_module_decl->name, "inner");
}

}  // namespace
