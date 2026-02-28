// §6.6.7: User-defined nettypes

#include "fixture_parser.h"
#include "elaborator/type_eval.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult6e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ModuleItem* FindNettypeDecl(ParseResult6e& r,
                                   std::string_view name = "") {
  if (!r.cu) return nullptr;
  for (auto* mod : r.cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind == ModuleItemKind::kNettypeDecl) {
        if (name.empty() || item->name == name) return item;
      }
    }
  }
  return nullptr;
}

struct ParseResult6f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6f Parse(const std::string& src) {
  ParseResult6f result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =============================================================================
// LRM section 6.6.7 -- User-defined nettypes
// =============================================================================
// §6.6.7: Basic nettype declaration with a simple built-in data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithIntType) {
  auto r = Parse(
      "module m;\n"
      "  nettype int mynet;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt = FindNettypeDecl(r);
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "mynet");
}

}  // namespace
