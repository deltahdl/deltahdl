// §23.2: Module definitions

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

// Returns true if any item in the list matches the given kind.
bool HasItemKind(const std::vector<ModuleItem *> &items, ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// Returns true if any item matches the given kind and name.
bool HasItemKindNamed(const std::vector<ModuleItem *> &items,
                      ModuleItemKind kind, std::string_view name) {
  for (auto *item : items) {
    if (item->kind == kind && item->name == name) return true;
  }
  return false;
}

namespace {

// extern_tf_declaration inside a module (interface_or_generate_item applies
// to modules too via module_or_generate_item).
TEST(SourceText, ExternFunctionPrototypeInModule) {
  auto r = Parse(
      "module m;\n"
      "  extern function int compute(input int a, input int b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto *mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mod->items[0]->name, "compute");
  EXPECT_TRUE(mod->items[0]->is_extern);
  EXPECT_TRUE(mod->items[0]->func_body_stmts.empty());
}

}  // namespace
