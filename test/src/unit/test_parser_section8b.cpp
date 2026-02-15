#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

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

// =============================================================================
// Section 8.2 -- Data type syntax
// =============================================================================

// Integer vector types with packed dimensions.
TEST(ParserSection8, DataTypeSyntaxIntegerVector) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  bit [15:0] addr;\n"
      "  reg [3:0] nibble;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 3u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[0]->name, "data");
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(items[1]->name, "addr");
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(items[2]->name, "nibble");
}

// Integer atom types.
TEST(ParserSection8, DataTypeSyntaxIntegerAtom) {
  auto r = Parse(
      "module m;\n"
      "  byte b;\n"
      "  shortint si;\n"
      "  int i;\n"
      "  longint li;\n"
      "  integer ig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 5u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(items[3]->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(items[4]->data_type.kind, DataTypeKind::kInteger);
}

// Non-integer types (real, shortreal, realtime).
TEST(ParserSection8, DataTypeSyntaxNonInteger) {
  auto r = Parse(
      "module m;\n"
      "  real r;\n"
      "  shortreal sr;\n"
      "  realtime rt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 3u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kShortreal);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kRealtime);
}

// =============================================================================
// Section 8.6 -- String data type
// =============================================================================

// Module-level string variable declaration.
TEST(ParserSection8, StringTypeModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  string name;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_EQ(item->name, "name");
}

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
TEST(ParserSection8, TypeOfThisReturnType) {
  EXPECT_TRUE(
      ParseOk("class Singleton #(type T = int);\n"
              "  static function type(this) get();\n"
              "  endfunction\n"
              "endclass\n"));
}

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

// Size cast: N'(expr).
TEST(ParserSection8, SizeCastExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    logic [31:0] wide;\n"
              "    logic [7:0] narrow;\n"
              "    narrow = 8'(wide);\n"
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

// =============================================================================
// Section 8.25 -- Enums
// =============================================================================

// Anonymous enum variable declaration with member inspection.
TEST(ParserSection8, EnumAnonymousDeclMembers) {
  auto r = Parse(
      "module m;\n"
      "  enum {IDLE, RUNNING, DONE} state;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(item->name, "state");
  ASSERT_EQ(item->data_type.enum_members.size(), 3u);
  EXPECT_EQ(item->data_type.enum_members[0].name, "IDLE");
  EXPECT_EQ(item->data_type.enum_members[1].name, "RUNNING");
  EXPECT_EQ(item->data_type.enum_members[2].name, "DONE");
}

// Enum with explicit base type and value assignments.
TEST(ParserSection8, EnumExplicitBaseTypeValues) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  enum bit [3:0] {BRONZE = 4'h3, SILVER, GOLD = 4'h5}"
              " medal;\n"
              "endmodule\n"));
}

// Typedef enum used as a named type for variable declarations.
TEST(ParserSection8, EnumTypedefUsage) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {NO, YES} boolean;\n"
      "  boolean flag;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(items[0]->name, "boolean");
  EXPECT_EQ(items[0]->typedef_type.enum_members.size(), 2u);
  EXPECT_EQ(items[1]->name, "flag");
}

// =============================================================================
// Section 8.26 -- Class types
// =============================================================================

// Interface class declaration with pure virtual method.
TEST(ParserSection8, InterfaceClassDecl) {
  auto r = Parse(
      "interface class PutIf;\n"
      "  pure virtual function void put(int val);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "PutIf");
}

// Class implementing multiple interface classes.
TEST(ParserSection8, ClassImplementsMultipleInterfaces) {
  EXPECT_TRUE(
      ParseOk("interface class A;\n"
              "  pure virtual function void fa();\n"
              "endclass\n"
              "interface class B;\n"
              "  pure virtual function void fb();\n"
              "endclass\n"
              "class C implements A, B;\n"
              "  virtual function void fa();\n"
              "  endfunction\n"
              "  virtual function void fb();\n"
              "  endfunction\n"
              "endclass\n"));
}

// Forward typedef class followed by full class definition.
TEST(ParserSection8, ForwardTypedefClassSelfRef) {
  auto r = Parse(
      "typedef class Node;\n"
      "class Node;\n"
      "  Node next;\n"
      "  int data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Node");
}
