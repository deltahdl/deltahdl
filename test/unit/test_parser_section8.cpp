#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// §8 Class declarations — parsing
// =============================================================================

TEST(ParserSection8, EmptyClassDecl) {
  auto r = Parse("class Packet; endclass");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_TRUE(r.cu->classes[0]->members.empty());
}

TEST(ParserSection8, ClassWithProperties) {
  auto r = Parse(
      "class Packet;\n"
      "  int header;\n"
      "  int payload;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 2u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "header");
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[1]->name, "payload");
}

TEST(ParserSection8, ClassWithMethod) {
  auto r = Parse(
      "class Packet;\n"
      "  int data;\n"
      "  function int get_data();\n"
      "    return data;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  bool found_method = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      found_method = true;
      ASSERT_NE(m->method, nullptr);
    }
  }
  EXPECT_TRUE(found_method);
}

TEST(ParserSection8, ClassExtends) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "Base");
  EXPECT_TRUE(r.cu->classes[0]->base_class.empty());
  EXPECT_EQ(r.cu->classes[1]->name, "Derived");
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
}

TEST(ParserSection8, VirtualClass) {
  auto r = Parse(
      "virtual class AbstractBase;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

TEST(ParserSection8, ClassWithQualifiers) {
  auto r = Parse(
      "class MyClass;\n"
      "  local int secret;\n"
      "  protected int hidden;\n"
      "  static int shared;\n"
      "  rand int random_val;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 4u);
  EXPECT_TRUE(cls->members[0]->is_local);
  EXPECT_TRUE(cls->members[1]->is_protected);
  EXPECT_TRUE(cls->members[2]->is_static);
  EXPECT_TRUE(cls->members[3]->is_rand);
}

TEST(ParserSection8, ClassWithTask) {
  auto r = Parse(
      "class MyClass;\n"
      "  task do_stuff();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  bool found = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      found = true;
      ASSERT_NE(m->method, nullptr);
      EXPECT_EQ(m->method->kind, ModuleItemKind::kTaskDecl);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection8, ClassWithConstraint) {
  auto r = Parse(
      "class Constrained;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  bool found = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint) {
      found = true;
      EXPECT_EQ(m->name, "c1");
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection8, ClassWithInitializer) {
  auto r = Parse(
      "class WithInit;\n"
      "  int x = 42;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_NE(cls->members[0]->init_expr, nullptr);
}

TEST(ParserSection8, ClassEndLabel) {
  auto r = Parse(
      "class Labeled;\n"
      "endclass : Labeled\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Labeled");
}

TEST(ParserSection8, ClassWithVirtualMethod) {
  auto r = Parse(
      "class Base;\n"
      "  virtual function void display();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  bool found = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->is_virtual) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §8.5 — Parameterized classes
TEST(ParserSection8, ParameterizedClass) {
  auto r = Parse(
      "class stack #(parameter int DEPTH = 8);\n"
      "  int data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "stack");
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "DEPTH");
}

TEST(ParserSection8, ParameterizedClassMultipleParams) {
  auto r = Parse(
      "class fifo #(parameter int WIDTH = 8, parameter int DEPTH = 16);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 2u);
  EXPECT_EQ(cls->params[0].first, "WIDTH");
  EXPECT_EQ(cls->params[1].first, "DEPTH");
}

TEST(ParserSection8, ParameterizedClassTypeParam) {
  auto r = Parse(
      "class container #(type T = int);\n"
      "  T data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

// §8.5 — Parameterized class with extends
TEST(ParserSection8, ParameterizedClassExtends) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived #(parameter int N = 4) extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  EXPECT_EQ(cls->name, "Derived");
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "N");
  EXPECT_EQ(cls->base_class, "Base");
}

// §8.13 — Extends with constructor arguments
TEST(ParserSection8, ExtendsWithArgs) {
  auto r = Parse(
      "class Base;\n"
      "endclass\n"
      "class Child extends Base(1, 2);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
}

// §8.3 — Class inside module
TEST(ParserSection8, ClassInsideModule) {
  auto r = Parse(
      "module m;\n"
      "  class inner_cls;\n"
      "    int x;\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& items = r.cu->modules[0]->items;
  bool found = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      found = true;
      ASSERT_NE(item->class_decl, nullptr);
      EXPECT_EQ(item->class_decl->name, "inner_cls");
    }
  }
  EXPECT_TRUE(found);
}

// §8.5 — Parameterized class inside module (the sv-tests TIMEOUT case)
TEST(ParserSection8, ParameterizedClassInsideModule) {
  auto r = Parse(
      "module class_tb;\n"
      "  class test_cls #(parameter a = 12);\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& items = r.cu->modules[0]->items;
  bool found = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      found = true;
      ASSERT_NE(item->class_decl, nullptr);
      EXPECT_EQ(item->class_decl->name, "test_cls");
      ASSERT_EQ(item->class_decl->params.size(), 1u);
      EXPECT_EQ(item->class_decl->params[0].first, "a");
    }
  }
  EXPECT_TRUE(found);
}

// §8.26 — Typedef class (forward declaration)
TEST(ParserSection8, TypedefClass) {
  auto r = Parse(
      "typedef class MyClass;\n"
      "class MyClass;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "MyClass");
}

// §8.3 — Lifetime specifier on class
TEST(ParserSection8, ClassWithLifetime) {
  auto r = Parse(
      "class automatic MyClass;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "MyClass");
}

// §8.15 — Extends with scoped class name
TEST(ParserSection8, ExtendsScopedName) {
  auto r = Parse(
      "class Child extends pkg::Base;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  // Just verify it parses — scoped name stored as "Base" (last identifier)
  EXPECT_EQ(r.cu->classes[0]->name, "Child");
}

// §8.5 — Typedef inside class body (enum, struct)
TEST(ParserSection8, ClassWithTypedef) {
  auto r = Parse(
      "class test_cls;\n"
      "  typedef enum {A = 10, B = 20} e_type;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "test_cls");
}

// §8.5 — Parameter inside class body
TEST(ParserSection8, ClassWithParameter) {
  auto r = Parse(
      "class par_cls;\n"
      "  parameter int b = 23;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "par_cls");
}

// §8.5 — Localparam inside class body
TEST(ParserSection8, ClassWithLocalparam) {
  auto r = Parse(
      "class my_cls;\n"
      "  localparam int SIZE = 8;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "my_cls");
}

// §8.7 — Constructor (function new)
TEST(ParserSection8, ClassConstructor) {
  auto r = Parse(
      "class Packet;\n"
      "  int data;\n"
      "  function new();\n"
      "    data = 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  bool found = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      found = true;
      ASSERT_NE(m->method, nullptr);
      EXPECT_EQ(m->method->name, "new");
    }
  }
  EXPECT_TRUE(found);
}

// §8.7 — Constructor with parameters
TEST(ParserSection8, ClassConstructorWithParams) {
  auto r = Parse(
      "class Packet;\n"
      "  int data;\n"
      "  function new(int val);\n"
      "    data = val;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// §8.13 — Super.new() call
TEST(ParserSection8, ConstructorSuperNew) {
  auto r = Parse(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    super.new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
}

// §8.24 — Out-of-block method with scoped name
TEST(ParserSection8, OutOfBlockMethod) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls;\n"
      "    int a;\n"
      "    extern function void test_method(int val);\n"
      "  endclass\n"
      "  function void test_cls::test_method(int val);\n"
      "    a = val;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §8.21 — Pure virtual function (no body)
TEST(ParserSection8, PureVirtualFunction) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// §8.15 — Constructor end label
TEST(ParserSection8, ConstructorEndLabel) {
  auto r = Parse(
      "class Base;\n"
      "  function new();\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// §8.4 — Class instantiation with 'new' expression
TEST(ParserSection8, NewExpression) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls;\n"
      "    int a;\n"
      "  endclass\n"
      "  test_cls obj;\n"
      "  initial begin\n"
      "    obj = new;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §8.4 — Null comparison
TEST(ParserSection8, NullExpression) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls;\n"
      "    int a;\n"
      "  endclass\n"
      "  test_cls obj;\n"
      "  initial begin\n"
      "    if (obj == null) obj = new;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §8.7 — Constructor with arguments
TEST(ParserSection8, NewWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls;\n"
      "    int a;\n"
      "    function new(int val);\n"
      "      a = val;\n"
      "    endfunction\n"
      "  endclass\n"
      "  test_cls obj;\n"
      "  initial begin\n"
      "    obj = new(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §8.11 — 'this' keyword
TEST(ParserSection8, ThisExpression) {
  auto r = Parse(
      "class MyClass;\n"
      "  int data;\n"
      "  function void set(int data);\n"
      "    this.data = data;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// §8.15 — super.new() expression
TEST(ParserSection8, SuperNewExpression) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x);\n"
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

// §8.26.3 — Interface class with typedef member
TEST(ParserSection8, InterfaceClassWithTypedef) {
  auto r = Parse(
      "interface class ihello;\n"
      "  typedef int int_t;\n"
      "  pure virtual function void hello(int_t val);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "ihello");
}
