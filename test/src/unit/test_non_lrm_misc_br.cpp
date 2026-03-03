// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Returns the first class member of kind kMethod, or nullptr if not found.
static ClassMember* FindMethodMember(ClassDecl* cls) {
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      return m;
    }
  }
  return nullptr;
}

namespace {

// Class with extends.
TEST(SourceText, ClassWithExtends) {
  auto r = Parse("class Child extends Parent; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->base_class, "Parent");
}

// =============================================================================
// A.1.2 class_declaration — additional forms
// =============================================================================
// Class with final_specifier: class :final C;
TEST(SourceText, ClassWithFinal) {
  auto r = Parse("class :final C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_final);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

// class_constructor_declaration with super.new()
TEST(SourceText, ClassConstructorSuperNew) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x); endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new();\n"
      "    super.new(5);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
  EXPECT_EQ(r.cu->classes[1]->members[0]->method->name, "new");
}

TEST(Parser, ClassPropertyQualifiers) {
  auto r = Parse(
      "class pkt;\n"
      "  rand int data;\n"
      "  local int secret;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 2);
  EXPECT_TRUE(cls->members[0]->is_rand);
  EXPECT_TRUE(cls->members[1]->is_local);
}

// class_property ::= const { class_item_qualifier } data_type id [ = expr ] ;
TEST(SourceText, ClassConstProperty) {
  auto r = Parse(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  const static int SMAX = 200;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_TRUE(members[0]->is_const);
  EXPECT_EQ(members[0]->name, "MAX");
  EXPECT_NE(members[0]->init_expr, nullptr);
  EXPECT_TRUE(members[1]->is_const);
  EXPECT_TRUE(members[1]->is_static);
}

TEST(Parser, VirtualClass) {
  auto r = Parse("virtual class base; endclass");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

// class_method ::= pure virtual { class_item_qualifier } method_prototype ;
//                | extern { method_qualifier } method_prototype ;
TEST(SourceText, ClassPureVirtualAndExtern) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function void pv_fn();\n"
      "  pure virtual task pv_task();\n"
      "  extern function void ext_fn();\n"
      "  extern static task ext_task();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[3]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(members[0]->is_virtual);
  EXPECT_TRUE(members[1]->is_virtual);
  EXPECT_EQ(members[2]->method->name, "ext_fn");
  EXPECT_TRUE(members[3]->is_static);
}

TEST(ParserA26, FuncPrototypePureVirtual) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function int compute(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskPrototypePureVirtual) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual task do_work(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 21. Class scope resolution (cls::member)
TEST(ParserClause03, Cl3_13_ClassScopeResolution) {
  EXPECT_TRUE(
      ParseOk("class base;\n"
              "  typedef int my_type;\n"
              "endclass\n"
              "module m;\n"
              "  base::my_type x;\n"
              "endmodule\n"));
}

// class_type (ps_class_identifier [param] { :: class_identifier [param] })
TEST(ParserA221, DataTypeClassType) {
  auto r = Parse(
      "class my_cls;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m; my_cls::my_type x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// method_prototype ::= task_prototype | function_prototype
TEST(SourceText, ClassMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern function int get_val();\n"
      "  extern task do_work();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0]->method->name, "get_val");
  EXPECT_EQ(members[1]->method->name, "do_work");
}

// ---------------------------------------------------------------------------
// function_body_declaration (scope qualifiers)
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncBodyOutOfBlockConstructor) {
  auto r = Parse(
      "class C;\n"
      "  extern function new();\n"
      "endclass\n"
      "function C::new();\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// task_body_declaration (scope qualifiers)
// ---------------------------------------------------------------------------
TEST(ParserA27, TaskBodyClassScope) {
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

TEST(ParserA27, TaskBodyOutOfBlockMethod) {
  auto r = Parse(
      "class C;\n"
      "  extern task run();\n"
      "endclass\n"
      "task C::run();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Class with parameters.
TEST(SourceText, ClassWithParams) {
  auto r = Parse("class C #(type T = int); endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->params.size(), 1u);
}

// class_item ::= { attribute_instance } interface_class_declaration
TEST(SourceText, ClassNestedInterfaceClass) {
  auto r = Parse(
      "class Outer;\n"
      "  interface class IFace;\n"
      "    pure virtual function void do_it();\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_TRUE(members[0]->nested_class->is_interface);
}

// interface_class_item ::= type_declaration | interface_class_method | params
TEST(SourceText, InterfaceClassItems) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void do_thing();\n"
      "  pure virtual task do_task();\n"
      "  typedef int my_int;\n"
      "  localparam int LP = 5;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(members[0]->is_virtual);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kTypedef);
  EXPECT_EQ(members[3]->kind, ClassMemberKind::kProperty);
}

// interface_class_declaration: interface class.
TEST(SourceText, InterfaceClassDecl) {
  auto r = Parse("interface class IC; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "IC");
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
  const std::string kExpectedNames[] = {"header", "payload"};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(cls->members[i]->kind, ClassMemberKind::kProperty);
    EXPECT_EQ(cls->members[i]->name, kExpectedNames[i]);
  }
}

TEST(ParserSection8, ClassExtendsBase) {
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
}

TEST(ParserSection8, ClassExtendsDerived) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->name, "Derived");
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
}

TEST(ParserSection8, ClassWithQualifiersLocalProtected) {
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
}

TEST(ParserSection8, ClassWithQualifiersStaticRand) {
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
  auto* m = FindMethodMember(r.cu->classes[0]);
  ASSERT_NE(m, nullptr);
  ASSERT_NE(m->method, nullptr);
  EXPECT_EQ(m->method->kind, ModuleItemKind::kTaskDecl);
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

}  // namespace
