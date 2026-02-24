// §16.12.18: Typed formal arguments in property declarations

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

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

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Production #17: property_formal_type
// property_formal_type ::= sequence_formal_type | property
// =============================================================================
TEST(ParserA210, PropertyFormalType_Property) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(property q);\n"
              "    q;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyFormalType_Sequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(sequence s);\n"
              "    s |-> 1;\n"
              "  endproperty\n"
              "endmodule\n"));
}

}  // namespace
