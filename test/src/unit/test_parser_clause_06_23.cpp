// §6.23: Type operator

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

namespace {

// type_reference (type(expression) | type(data_type))
TEST(ParserA221, DataTypeTypeReference) {
  // A.2.2.1: data_type ::= ... | type_reference
  // type(expr) used as data_type in a declaration (without 'var' prefix)
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  type(a) b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_NE(item->data_type.type_ref_expr, nullptr);
}

// --- type_reference ---
// type ( expression ) | type ( data_type_or_incomplete_class_scoped_type )
TEST(ParserA221, TypeRefExpression) {
  // type(expression) in expression context
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  initial begin $display(\"%s\", $typename(type(a))); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, TypeRefDataType) {
  // type(data_type) in expression context
  auto r = Parse(
      "module m;\n"
      "  initial begin $display(\"%s\", $typename(type(logic [7:0]))); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- incomplete_class_scoped_type ---
// type_identifier :: type_identifier_or_class_type
// (used within type_reference context for unresolved class scopes)
TEST(ParserA221, IncompleteClassScopedType) {
  // type(A::B) where A is used as a scope but may not be fully resolved
  auto r = Parse(
      "class outer;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin $display(\"%s\", $typename(type(outer::inner_t))); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
