#include "fixture_parser.h"

using namespace delta;

namespace {

static ClassMember* FindMethodMember(ClassDecl* cls) {
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      return m;
    }
  }
  return nullptr;
}

// === Existing tests ===

TEST(ClassItemsParsing, Constructor) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, ConstructorWithArgs) {
  auto r = Parse(
      "class C;\n"
      "  function new(int val);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, ConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  constraint valid_range;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, ConstraintDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, NestedClass) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int x;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, ClassCovergroup) {
  auto r = Parse(
      "class C;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, InterfaceClassItems) {
  auto r = Parse(
      "interface class IFace;\n"
      "  pure virtual function void do_work();\n"
      "  typedef int myint;\n"
      "  localparam int SIZE = 4;\n"
      "  parameter int W = 8;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
}

// --- Moved from test_parser_clause_08_07.cpp ---

TEST(ClassItemsParsing, ClassConstructor) {
  auto r = Parse(
      "class Packet;\n"
      "  int data;\n"
      "  function new();\n"
      "    data = 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = FindMethodMember(r.cu->classes[0]);
  ASSERT_NE(m, nullptr);
  ASSERT_NE(m->method, nullptr);
  EXPECT_EQ(m->method->name, "new");
}

TEST(ClassItemsParsing, ClassConstructorWithParams) {
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

TEST(ClassItemsParsing, ClassConstructorDecl) {
  auto r = Parse(
      "class C;\n"
      "  function new(int val);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[0]->method->name, "new");
}

TEST(ClassItemsParsing, SimpleConstructorDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, ConstructorDeclarationWithEndLabel) {
  auto r = Parse(
      "class C;\n"
      "  function new(int x);\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, ConstructorDefaultArgs) {
  auto r = Parse(
      "class Packet;\n"
      "  int command;\n"
      "  int address;\n"
      "  function new(int cmd = 0, bit [12:0] adrs = 0);\n"
      "    command = cmd;\n"
      "    address = adrs;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  auto* m = FindMethodMember(cls);
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->method->name, "new");
  ASSERT_GE(m->method->func_args.size(), 2u);
  EXPECT_NE(m->method->func_args[0].default_value, nullptr);
  EXPECT_NE(m->method->func_args[1].default_value, nullptr);
}

TEST(ClassItemsParsing, ConstructorEndLabel) {
  auto r = Parse(
      "class Base;\n"
      "  function new();\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ClassItemsParsing, ConstructorLocalQualifierLegal) {
  ParseOk(
      "class C;\n"
      "  local function new();\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(ClassItemsParsing, ConstructorProtectedQualifierLegal) {
  ParseOk(
      "class C;\n"
      "  protected function new(int x);\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(ClassItemsParsing, ConstructorStaticError) {
  auto r = Parse(
      "class C;\n"
      "  static function new();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassItemsParsing, ConstructorVirtualError) {
  auto r = Parse(
      "class C;\n"
      "  virtual function new();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassItemsParsing, ConstructorSuperNewCall) {
  ParseOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new();\n"
      "    super.new();\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(ClassItemsParsing, ConstructorSuperNewWithArgs) {
  ParseOk(
      "class Base;\n"
      "  int x;\n"
      "  function new(int val);\n"
      "    x = val;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new;\n"
      "    super.new(42);\n"
      "  endfunction\n"
      "endclass\n");
}

// --- Moved from test_parser_clause_08_03.cpp ---

TEST(ClassItemsParsing, ConstructorDefaultArg) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(default);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  ASSERT_EQ(members[0]->method->func_args.size(), 1u);
  EXPECT_TRUE(members[0]->method->func_args[0].is_default);
}

TEST(ClassItemsParsing, ErrorDuplicateDefaultInConstructorArgs) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(default, int x, default);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// --- Moved from test_parser_clause_08_17.cpp ---

TEST(ClassItemsParsing, ConstructorSuperNew) {
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

TEST(ClassItemsParsing, SuperNewExpression) {
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

TEST(ClassItemsParsing, ConstructorChainingDefault) {
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

TEST(ClassItemsParsing, SuperNewWithMultipleArgs) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  function new(string name, int id);\n"
              "  endfunction\n"
              "endclass\n"
              "class Child extends Base;\n"
              "  function new();\n"
              "    super.new(\"foo\", 42);\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ClassItemsParsing, ConstructorMixedArgsWithDefault) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(int size, default);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& args = r.cu->classes[0]->members[0]->method->func_args;
  ASSERT_EQ(args.size(), 2u);
  EXPECT_FALSE(args[0].is_default);
  EXPECT_EQ(args[0].name, "size");
  EXPECT_TRUE(args[1].is_default);
}

TEST(ClassItemsParsing, ConstructorDefaultBeforeArgs) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(default, bit enable);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto& args = r.cu->classes[0]->members[0]->method->func_args;
  ASSERT_EQ(args.size(), 2u);
  EXPECT_TRUE(args[0].is_default);
  EXPECT_FALSE(args[1].is_default);
}

// --- Moved from test_parser_clause_08_23.cpp ---

TEST(ClassItemsParsing, ClassNestedClass) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int val;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_EQ(members[0]->nested_class->name, "Inner");
}

TEST(ClassItemsParsing, ClassWithTypedef) {
  auto r = Parse(
      "class test_cls;\n"
      "  typedef enum {A = 10, B = 20} e_type;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "test_cls");
}

TEST(ClassItemsParsing, NestedClassWithInstance) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int x;\n"
      "  endclass\n"
      "  Inner inst;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Outer");
}

// --- Moved from test_parser_clause_08_26_08.cpp ---

TEST(ClassItemsParsing, InterfaceMethodDefaultArgs) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
              "  pure virtual function void foo(int a = 5);\n"
              "endclass\n"));
}

TEST(ClassItemsParsing, InterfaceMethodMultipleDefaultArgs) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
              "  pure virtual function int calc(int a = 0, int b = 1);\n"
              "endclass\n"));
}

// --- Moved from test_parser_annex_a_10.cpp ---

TEST(ClassItemsParsing, ClassNewWithDefaultArg) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  int x;\n"
              "  function new(int a = 0);\n"
              "    x = a;\n"
              "  endfunction\n"
              "endclass\n"));
}

// --- Missing coverage tests ---

TEST(ClassItemsParsing, ConstructorNoParens) {
  auto r = Parse(
      "class C;\n"
      "  function new;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->method->name, "new");
}

TEST(ClassItemsParsing, ConstructorSuperNewDefault) {
  ParseOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new();\n"
      "    super.new(default);\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(ClassItemsParsing, InterfaceClassPureVirtualTask) {
  ParseOk(
      "interface class IC;\n"
      "  pure virtual task run();\n"
      "endclass\n");
}

TEST(ClassItemsParsing, ExternConstructorPrototypeNoArgs) {
  auto r = Parse(
      "class C;\n"
      "  extern function new;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->method->name, "new");
}

TEST(ClassItemsParsing, NestedInterfaceClassDeclaration) {
  auto r = Parse(
      "class Outer;\n"
      "  interface class Inner;\n"
      "    pure virtual function void work();\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
