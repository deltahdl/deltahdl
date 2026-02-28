// §6.8: on variable initialization). This is roughly equivalent to a C
// automatic variable.

#include "fixture_parser.h"

using namespace delta;

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

TEST(ParserAnnexA, A2VarDeclWithInit) {
  auto r = Parse("module m; logic [7:0] data = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

TEST(ParserA213, DataDeclMultipleAssign) {
  // list_of_variable_decl_assignments: multiple names
  auto r = Parse("module m; int a = 1, b = 2; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 2);
}

// [class_scope | package_scope] type_identifier {packed_dimension}
TEST(ParserA221, DataTypeScopedType) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int my_int_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  pkg::my_int_t x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA23, ListOfVariableDeclAssignmentsWithDims) {
  auto r = Parse("module m; logic [7:0] mem [256], cache [64]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 2);
}

struct ParseResult6j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6j Parse(const std::string& src) {
  ParseResult6j result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6j& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// 4. Int variable declaration.
TEST(ParserSection6, Sec6_5_IntVarDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  int count;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "count");
}

// 11. Variable with initialization (logic v = 0).
TEST(ParserSection6, Sec6_5_LogicVarInit) {
  auto r = Parse(
      "module t;\n"
      "  logic v = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(item->data_type.is_net);
  ASSERT_NE(item->init_expr, nullptr);
}

}  // namespace
