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

// §8.3 — Covergroup inside class
TEST(ParserSection8, CovergroupInClass) {
  auto r = Parse(
      "class CoveredClass;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// §8.3 — Multiple properties on one line (comma-separated)
TEST(ParserSection8, MultiplePropertiesCommaSeparated) {
  auto r = Parse(
      "class MyClass;\n"
      "  int a, b, c;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 3u);
  const std::string kExpectedNames[] = {"a", "b", "c"};
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(cls->members[i]->name, kExpectedNames[i]);
  }
}

// §8.17 — Chaining constructors with super.new() and default
TEST(ParserSection8, ConstructorChainingDefault) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x = 0);\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    super.new(5);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
}

// §8.3 — Randc qualifier
TEST(ParserSection8, RandcQualifier) {
  auto r = Parse(
      "class Die;\n"
      "  randc bit [2:0] face;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_randc);
}

// §8.18 — Extern constraint declaration
TEST(ParserSection8, ExternConstraintDecl) {
  auto r = Parse(
      "class A;\n"
      "  rand int x;\n"
      "  extern constraint c1;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  bool found = false;
  for (auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == "c1") {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §8.26.2 — Extends and implements together
TEST(ParserSection8, ExtendsAndImplements) {
  auto r = Parse(
      "interface class Iface;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class Base;\n"
      "endclass\n"
      "class Child extends Base implements Iface;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 3u);
  EXPECT_EQ(r.cu->classes[2]->base_class, "Base");
}

// §8.9 — Static property with const
TEST(ParserSection8, StaticConstProperty) {
  auto r = Parse(
      "class Config;\n"
      "  static const int VERSION = 3;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_TRUE(cls->members[0]->is_const);
}

// =============================================================================
// §8.23 -- Class scope resolution operator ::
// =============================================================================
TEST(ParserSection8, ClassScopeResolutionStaticMethod) {
  auto r = Parse(
      "class Base;\n"
      "  static function void display();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial Base::display();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection8, ClassScopeResolutionEnum) {
  auto r = Parse(
      "class Base;\n"
      "  typedef enum {bin, oct, dec, hex} radix;\n"
      "endclass\n"
      "module m;\n"
      "  initial x = Base::bin;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection8, ClassScopeResolutionTypedef) {
  auto r = Parse(
      "class Outer;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m;\n"
      "  Outer::my_type x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection8, ClassScopeResolutionParameter) {
  auto r = Parse(
      "class Cfg;\n"
      "  parameter int WIDTH = 8;\n"
      "endclass\n"
      "module m;\n"
      "  logic [Cfg::WIDTH-1:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// §8.25 -- Parameterized classes (additional tests)
// =============================================================================
TEST(ParserSection8, ParameterizedClassSpecialization) {
  auto r = Parse(
      "class vector #(int size = 1);\n"
      "  bit [size-1:0] a;\n"
      "endclass\n"
      "module m;\n"
      "  vector #(10) vten;\n"
      "  vector #(.size(2)) vtwo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection8, ParameterizedClassStackType) {
  auto r = Parse(
      "class stack #(type T = int);\n"
      "  T items[];\n"
      "  function void push(T a);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

TEST(ParserSection8, ParameterizedClassDefaultInstantiation) {
  auto r = Parse(
      "class stack #(type T = int);\n"
      "  T items[];\n"
      "endclass\n"
      "module m;\n"
      "  stack is_default;\n"
      "  stack #(real) rs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
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
