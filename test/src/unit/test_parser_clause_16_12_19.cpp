// §16.12.19: Local variable formal arguments in property declarations

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
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Productions #14-#16: property_port_list, property_port_item,
//     property_lvar_port_direction
// property_port_item ::=
//     { attribute_instance } [ local [ property_lvar_port_direction ] ]
//     property_formal_type formal_port_identifier { variable_dimension }
//     [ = property_actual_arg ]
// property_lvar_port_direction ::= input
// =============================================================================
TEST(ParserA210, PropertyPortItem_LocalInput) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(local input int x);\n"
              "    x > 0;\n"
              "  endproperty\n"
              "endmodule\n"));
}

}  // namespace
