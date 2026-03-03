// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult8b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult8b Parse(const std::string& src) {
  ParseResult8b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult8b& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt* FirstInitialStmt(ParseResult8b& r) {
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

namespace {

// String variable with initializer.
TEST(ParserSection8, StringTypeWithInit) {
  auto r = Parse(
      "module m;\n"
      "  string greeting = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_NE(item->init_expr, nullptr);
}

// String variable inside block-level declaration.
TEST(ParserSection8, StringTypeBlockLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    string s;\n"
      "    s = \"world\";\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kString);
}

// =============================================================================
// Section 8.10 -- Type parameters
// =============================================================================
// Module with type parameter.
TEST(ParserSection8, TypeParameterModule) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = int);\n"
              "  T data;\n"
              "endmodule\n"));
}

// Module with type parameter defaulting to logic vector.
TEST(ParserSection8, TypeParameterLogicVector) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = logic [7:0]);\n"
              "  T bus;\n"
              "endmodule\n"));
}

// Class with type parameter used as member type.
TEST(ParserSection8, TypeParameterClassMember) {
  auto r = Parse(
      "class container #(type T = int);\n"
      "  T value;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

// =============================================================================
// Section 8.11 -- Type compatibility (this keyword, type(this))
// =============================================================================
// Use of 'this' to access class properties.
TEST(ParserSection8, ThisKeywordPropertyAccess) {
  EXPECT_TRUE(
      ParseOk("class MyClass;\n"
              "  int value;\n"
              "  function void set_value(int value);\n"
              "    this.value = value;\n"
              "  endfunction\n"
              "endclass\n"));
}

// Use of type(this) as return type for singleton pattern.
// =============================================================================
// Section 8.16 -- Casting
// =============================================================================
// $cast system call with class handles.
TEST(ParserSection8, DynamicCastClassHandles) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class Base;\n"
              "    int x;\n"
              "  endclass\n"
              "  class Derived extends Base;\n"
              "    int y;\n"
              "  endclass\n"
              "  initial begin\n"
              "    Base b;\n"
              "    Derived d;\n"
              "    d = new;\n"
              "    b = d;\n"
              "    $cast(d, b);\n"
              "  end\n"
              "endmodule\n"));
}

// Static cast with type apostrophe syntax: type'(expr).
TEST(ParserSection8, StaticCastTypeSyntax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    int a;\n"
              "    real r;\n"
              "    r = 3.14;\n"
              "    a = int'(r);\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// Section 8.18 -- User-defined types (typedef)
// =============================================================================
// Simple typedef of built-in type.
TEST(ParserSection8, TypedefSimpleBuiltin) {
  auto r = Parse(
      "module m;\n"
      "  typedef int my_int;\n"
      "  my_int x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(items[0]->name, "my_int");
}

// Forward typedef declaration for enum.
TEST(ParserSection8, TypedefForwardEnum) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum my_enum;\n"
              "  typedef enum {A, B, C} my_enum;\n"
              "endmodule\n"));
}

// Typedef of enum with named type for reuse.
TEST(ParserSection8, TypedefEnumWithMembers) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(items[0]->typedef_type.kind, DataTypeKind::kEnum);
}

}  // namespace
