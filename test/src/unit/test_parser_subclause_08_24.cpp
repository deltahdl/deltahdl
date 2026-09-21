#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;
namespace {

TEST(ClassParsing, OutOfBlockMethod) {
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

// A.1.6's interface_or_generate_item is the one body production that admits
// an extern_tf_declaration, so the prototype is hosted in an interface.
TEST(FunctionDeclParsing, FuncPrototypeExtern) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function int foo(input int x);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->name, "foo");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(OutOfBlockDeclParsing, FuncBodyMethodClassStored) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "foo") {
      EXPECT_EQ(item->method_class, "C");
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(FunctionDeclParsing, FuncBodyOutOfBlockConstructor) {
  auto r = Parse(
      "class C;\n"
      "  extern function new();\n"
      "endclass\n"
      "function C::new();\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// An out-of-block task body repeating the prototype's tf_port_list.
// test_parser_annex_a_02_07.cpp covers the class_scope form that has no
// parenthesized port list.
TEST(TaskDeclParsing, TaskBodyClassScopeWithPortList) {
  auto r = Parse(
      "class C;\n"
      "  extern task my_task(input int x);\n"
      "endclass\n"
      "task C::my_task(input int x);\n"
      "  $display(\"x=%0d\", x);\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OutOfBlockDeclParsing, TaskBodyMethodClassStored) {
  auto r = Parse(
      "class C;\n"
      "  extern task run();\n"
      "endclass\n"
      "task C::run();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kTaskDecl && item->name == "run") {
      EXPECT_EQ(item->method_class, "C");
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(OutOfBlockDeclParsing, RegularFuncNoMethodClass) {
  auto r = Parse(
      "function int bar();\n"
      "  return 0;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "bar") {
      EXPECT_TRUE(item->method_class.empty());
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(OutOfBlockDeclParsing, ReturnTypeClassScopeResolution) {
  auto r = Parse(
      "class C;\n"
      "  typedef int T;\n"
      "  extern function T f();\n"
      "endclass\n"
      "function C::T C::f();\n"
      "  return 1;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "f") {
      EXPECT_EQ(item->method_class, "C");
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(OutOfBlockDeclParsing, ExternPrototypeNotStoredAsFuncBody) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo(int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_NE(cls, nullptr);
  bool found = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "foo") {
      EXPECT_TRUE(m->method->is_extern);
      EXPECT_TRUE(m->method->func_body_stmts.empty());
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(OutOfBlockDeclParsing, OutOfBlockDropsQualifiers) {
  auto r = Parse(
      "class Packet;\n"
      "  Packet next;\n"
      "  function Packet get_next();\n"
      "    get_next = next;\n"
      "  endfunction\n"
      "  extern protected virtual function int send(int value);\n"
      "endclass\n"
      "function int Packet::send(int value);\n"
      "  return value;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "send") {
      EXPECT_EQ(item->method_class, "Packet");
      EXPECT_FALSE(item->is_extern);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(OutOfBlockDeclParsing, MultipleExternPrototypes) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "  extern task bar();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 0;\n"
      "endfunction\n"
      "task C::bar();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->cu_items) {
    if (!item->method_class.empty()) {
      EXPECT_EQ(item->method_class, "C");
      count++;
    }
  }
  EXPECT_EQ(count, 2);
}

TEST(OutOfBlockDeclParsing, OutOfBlockWithArguments) {
  auto r = Parse(
      "class C;\n"
      "  extern function int add(int a, int b);\n"
      "endclass\n"
      "function int C::add(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "add") {
      EXPECT_EQ(item->method_class, "C");
      EXPECT_EQ(item->func_args.size(), 2u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(OutOfBlockDeclParsing, RegularTaskNoMethodClass) {
  auto r = Parse(
      "task my_task();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kTaskDecl && item->name == "my_task") {
      EXPECT_TRUE(item->method_class.empty());
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §8.24 has an out-of-block method declaration access every declaration of the
// class whose prototype it implements, its example resolving the `T` of
// `function void C::f(T x)` to `C::T` (printed pages 202 and 203 of ~/IEEE
// 1800-2023.pdf). The parser decides whether an identifier opens a declaration
// by the type names it knows where it stands, and the class's own names leave
// at `endclass`, so the method's argument list and body have to be given them
// back: before that, `pair_t p;` was read as an expression statement and
// reported "expected ';', got identifier".
TEST(OutOfBlockDeclParsing, BodyReadsTheClassTypedefAsAType) {
  auto r = Parse(
      "class C;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  extern function void f();\n"
      "endclass\n"
      "function void C::f();\n"
      "  pair_t p;\n"
      "  p.a = 1;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* f = FindItemByName(r.cu->cu_items, "f");
  ASSERT_NE(f, nullptr);
  ASSERT_EQ(f->func_body_stmts.size(), 2u);
  EXPECT_EQ(f->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(f->func_body_stmts[0]->var_name, "p");
  EXPECT_EQ(f->func_body_stmts[0]->var_decl_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(f->func_body_stmts[0]->var_decl_type.type_name, "pair_t");
}

TEST(OutOfBlockDeclParsing, ArgumentListReadsTheClassTypedefAsAType) {
  auto r = Parse(
      "class C;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  extern function int g(pair_t p);\n"
      "endclass\n"
      "function int C::g(pair_t p);\n"
      "  return p.a;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindItemByName(r.cu->cu_items, "g");
  ASSERT_NE(g, nullptr);
  ASSERT_EQ(g->func_args.size(), 1u);
  EXPECT_EQ(g->func_args[0].name, "p");
  EXPECT_EQ(g->func_args[0].data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(g->func_args[0].data_type.type_name, "pair_t");
}

TEST(OutOfBlockDeclParsing, TaskBodyReadsTheClassTypedefAsAType) {
  auto r = Parse(
      "class C;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  extern task t(pair_t q);\n"
      "endclass\n"
      "task C::t(pair_t q);\n"
      "  pair_t p;\n"
      "  p = q;\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* t = FindItemByName(r.cu->cu_items, "t");
  ASSERT_NE(t, nullptr);
  ASSERT_EQ(t->func_args.size(), 1u);
  EXPECT_EQ(t->func_args[0].data_type.type_name, "pair_t");
  ASSERT_EQ(t->func_body_stmts.size(), 2u);
  EXPECT_EQ(t->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(t->func_body_stmts[0]->var_decl_type.type_name, "pair_t");
}

// §23.9 makes the function its own scope, so the class's names given to the
// method leave with it at `endfunction`: A.10.3 lets `data_type_or_implicit`
// be empty, so the `localparam pair_t = 1` after it is a value parameter named
// pair_t, which a leaked type name would read as a type and report at `=`.
TEST(OutOfBlockDeclParsing, ClassTypedefLeavesWithTheMethod) {
  auto r = Parse(
      "class C;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  extern function void f();\n"
      "endclass\n"
      "function void C::f();\n"
      "  pair_t p;\n"
      "endfunction\n"
      "localparam pair_t = 1;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByName(r.cu->cu_items, "pair_t");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

}  // namespace
