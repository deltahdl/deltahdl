// §6.23: Type operator

#include "fixture_parser.h"

using namespace delta;

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

// =============================================================================
// Section 8.23 -- Type-reference operator
// =============================================================================
// var type(expr) declaration.
TEST(ParserSection8, TypeRefVarDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real a = 1.0;\n"
              "  real b = 2.0;\n"
              "  var type(a + b) c;\n"
              "endmodule\n"));
}

// type(data_type) in parameter default.
TEST(ParserSection8, TypeRefDataTypeParam) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = type(logic [11:0]));\n"
              "endmodule\n"));
}

// type() comparison in expressions.
TEST(ParserSection8, TypeRefComparison) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) == type(int)) $display(\"int\");\n"
              "  end\n"
              "endmodule\n"));
}

struct ParseResult6b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6b Parse(const std::string& src) {
  ParseResult6b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult6b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// =========================================================================
// §6.23: Type operator
// =========================================================================
TEST(ParserSection6, TypeOperatorExpr_Kind) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTypeRef);
}

TEST(ParserSection6, TypeOperatorExpr_Inner) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->lhs->text, "y");
}

static ModuleItem* FirstItem(ParseResult6b& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

TEST(ParserSection6, TypeOperatorInDataType) {
  auto r = Parse(
      "module t;\n"
      "  parameter type T = type(int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  // The init_expr should be a type reference.
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kTypeRef);
}

// § primary — type_reference
TEST(ParserA84, PrimaryTypeRef) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    automatic int w;\n"
      "    w = $bits(x);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
