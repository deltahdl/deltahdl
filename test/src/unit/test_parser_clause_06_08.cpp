// §6.8: on variable initialization). This is roughly equivalent to a C
// automatic variable.

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

// =============================================================================
// A.2.1.3 Type declarations
// =============================================================================
// --- data_declaration ---
// [ const ] [ var ] [ lifetime ] data_type_or_implicit
//     list_of_variable_decl_assignments ;
// | type_declaration
// | package_import_declaration
// | nettype_declaration
TEST(ParserA213, DataDeclBasicVar) {
  auto r = Parse("module m; logic [7:0] data; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "data");
}

TEST(ParserA213, DataDeclVarPrefix) {
  // [var] data_type list
  auto r = Parse("module m; var logic x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
}

TEST(ParserA213, DataDeclLifetimeAutomatic) {
  // [lifetime] data_type list
  auto r = Parse("module m; automatic int counter; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserA213, DataDeclLifetimeStatic) {
  // [lifetime] data_type list
  auto r = Parse("module m; static int counter; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->is_static);
}

// --- list_of_variable_decl_assignments ---
// variable_decl_assignment { , variable_decl_assignment }
TEST(ParserA23, ListOfVariableDeclAssignmentsSingle) {
  auto r = Parse("module m; int x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kVarDecl);
}

TEST(ParserA23, ListOfVariableDeclAssignmentsMultiple) {
  auto r = Parse("module m; int a = 1, b = 2, c = 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 3);
}

// --- variable_decl_assignment ---
// variable_identifier { variable_dimension } [ = expression ]
// | dynamic_array_variable_identifier unsized_dimension { variable_dimension }
//   [ = dynamic_array_new ]
// | class_variable_identifier [ = class_new ]
TEST(ParserA24, VarDeclAssignmentBasic) {
  auto r = Parse("module m; int x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  EXPECT_EQ(item->init_expr, nullptr);
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

TEST(ParserA28, DataDeclMultiVarsInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a = 1, b = 2, c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->var_name, "a");
  EXPECT_EQ(body->stmts[1]->var_name, "b");
  EXPECT_EQ(body->stmts[2]->var_name, "c");
}

}  // namespace
