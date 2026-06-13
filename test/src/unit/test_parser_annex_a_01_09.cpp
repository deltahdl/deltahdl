// Observing tests for the BNF productions of IEEE 1800-2023 Annex A.1.9
// "Class items". Every production in this subclause is grammar that the parser
// already realizes; these tests pin the parser actually applying each rule by
// inspecting the resulting AST. The superscript markers in the LRM (e.g. on
// parameter_declaration, method_prototype, class_constructor_arg_list and the
// qualifier productions) point at clarification list elements in Annex A.10, a
// separate subclause, so they are not A.1.9's own requirements.

#include "fixture_parser.h"

using namespace delta;

namespace {

// Helpers to locate a class / member produced by the parser.
const ClassDecl* FirstClass(const ParseResult& r) {
  return r.cu->classes.empty() ? nullptr : r.cu->classes[0];
}

// --- class_item --------------------------------------------------------------
// class_item's class_declaration alternative: a class nested inside a class.
TEST(ClassItems, ClassItemNestedClassDeclaration) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kClassDecl);
  ASSERT_NE(c->members[0]->nested_class, nullptr);
  EXPECT_EQ(c->members[0]->nested_class->name, "Inner");
}

// class_item's covergroup_declaration alternative.
TEST(ClassItems, ClassItemCovergroupDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  covergroup cg;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kCovergroup);
}

// class_item's parameter_declaration ';' and local_parameter_declaration ';'
// alternatives both yield class properties named after the declared parameters.
TEST(ClassItems, ClassItemParameterAndLocalParam) {
  auto r = Parse(
      "class C;\n"
      "  parameter int P = 1;\n"
      "  localparam int Q = 2;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 2u);
  EXPECT_EQ(c->members[0]->name, "P");
  EXPECT_EQ(c->members[1]->name, "Q");
}

// class_item's empty ';' alternative: a stray semicolon is accepted and adds no
// member to the class body.
TEST(ClassItems, ClassItemEmptySemicolon) {
  auto r = Parse(
      "class C;\n"
      "  ;\n"
      "  int x;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->members.size(), 1u);
  EXPECT_EQ(c->members[0]->name, "x");
}

// class_item's interface_class_declaration alternative, distinct from the
// ordinary class_declaration alternative: an 'interface class' nested inside a
// class yields a class-declaration member flagged as an interface class.
TEST(ClassItems, ClassItemNestedInterfaceClassDeclaration) {
  auto r = Parse(
      "class Outer;\n"
      "  interface class Inner;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kClassDecl);
  ASSERT_NE(c->members[0]->nested_class, nullptr);
  EXPECT_TRUE(c->members[0]->nested_class->is_interface);
}

// Every class_item alternative permits a leading { attribute_instance }; the
// parser accepts the attribute prefix and parses the member that follows.
TEST(ClassItems, ClassItemWithAttributeInstance) {
  auto r = Parse(
      "class C;\n"
      "  (* my_attr *) int x;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(c->members[0]->name, "x");
}

// --- class_property ----------------------------------------------------------
// class_property's second alternative:
//   const {class_item_qualifier} data_type const_identifier [= constant_expression] ;
TEST(ClassItems, ClassPropertyConstForm) {
  auto r = Parse(
      "class C;\n"
      "  const int answer = 42;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_TRUE(c->members[0]->is_const);
  EXPECT_EQ(c->members[0]->name, "answer");
  EXPECT_NE(c->members[0]->init_expr, nullptr);
}

// class_property's const form leaves the '= constant_expression' initializer
// optional: a const property declared without an initializer is accepted.
TEST(ClassItems, ClassPropertyConstWithoutInitializer) {
  auto r = Parse(
      "class C;\n"
      "  const int c;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_TRUE(c->members[0]->is_const);
  EXPECT_EQ(c->members[0]->name, "c");
  EXPECT_EQ(c->members[0]->init_expr, nullptr);
}

// --- property_qualifier ------------------------------------------------------
// property_qualifier ::= random_qualifier | class_item_qualifier. Both branches
// can prefix a single data_declaration property.
TEST(ClassItems, PropertyQualifierRandAndStatic) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] a;\n"
      "  static int b;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 2u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_TRUE(c->members[0]->is_rand);
  EXPECT_EQ(c->members[1]->kind, ClassMemberKind::kProperty);
  EXPECT_TRUE(c->members[1]->is_static);
}

// --- random_qualifier --------------------------------------------------------
// random_qualifier ::= rand | randc.
TEST(ClassItems, RandomQualifierRandAndRandc) {
  auto r = Parse(
      "class C;\n"
      "  rand int a;\n"
      "  randc int b;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 2u);
  EXPECT_TRUE(c->members[0]->is_rand);
  EXPECT_FALSE(c->members[0]->is_randc);
  EXPECT_TRUE(c->members[1]->is_randc);
  EXPECT_FALSE(c->members[1]->is_rand);
}

// --- class_item_qualifier ----------------------------------------------------
// class_item_qualifier ::= static | protected | local.
TEST(ClassItems, ClassItemQualifierAccessModifiers) {
  auto r = Parse(
      "class C;\n"
      "  protected int a;\n"
      "  local int b;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 2u);
  EXPECT_TRUE(c->members[0]->is_protected);
  EXPECT_TRUE(c->members[1]->is_local);
}

// --- class_method ------------------------------------------------------------
// class_method's task_declaration and function_declaration alternatives.
TEST(ClassItems, ClassMethodFunctionAndTask) {
  auto r = Parse(
      "class C;\n"
      "  function int f();\n"
      "    return 0;\n"
      "  endfunction\n"
      "  task t();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 2u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(c->members[0]->method, nullptr);
  EXPECT_EQ(c->members[0]->method->name, "f");
  EXPECT_EQ(c->members[1]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(c->members[1]->method, nullptr);
  EXPECT_EQ(c->members[1]->method->name, "t");
}

// --- method_qualifier --------------------------------------------------------
// method_qualifier ::= [pure] virtual | class_item_qualifier. The plain
// 'virtual' branch (no 'pure') prefixes a complete method definition.
TEST(ClassItems, MethodQualifierVirtual) {
  auto r = Parse(
      "class C;\n"
      "  virtual function void f();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_TRUE(c->members[0]->is_virtual);
  EXPECT_FALSE(c->members[0]->is_pure_virtual);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kMethod);
}

// method_qualifier's class_item_qualifier branch (distinct from the [pure]
// virtual branch): an access qualifier may prefix a complete method definition.
TEST(ClassItems, MethodQualifierAccessModifier) {
  auto r = Parse(
      "class C;\n"
      "  protected function void f();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(c->members[0]->is_protected);
}

// class_method's 'pure virtual {class_item_qualifier} method_prototype ;'
// alternative — also exercises method_prototype's function_prototype branch.
TEST(ClassItems, ClassMethodPureVirtualPrototype) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function int f(int x);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_TRUE(c->members[0]->is_pure_virtual);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kMethod);
}

// class_method's 'extern {method_qualifier} method_prototype ;' alternative —
// covers both method_prototype branches (function_prototype and task_prototype).
TEST(ClassItems, ClassMethodExternPrototypes) {
  auto r = Parse(
      "class C;\n"
      "  extern function int f();\n"
      "  extern task t();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 2u);
  ASSERT_NE(c->members[0]->method, nullptr);
  EXPECT_TRUE(c->members[0]->method->is_extern);
  EXPECT_EQ(c->members[0]->method->name, "f");
  ASSERT_NE(c->members[1]->method, nullptr);
  EXPECT_TRUE(c->members[1]->method->is_extern);
  EXPECT_EQ(c->members[1]->method->name, "t");
}

// --- class_constructor_declaration -------------------------------------------
// class_constructor_declaration: 'function new (...) ; ... [super.new(...);] ...
// endfunction'. The constructor's name is recognized as "new".
TEST(ClassItems, ClassConstructorDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  function new(int x);\n"
      "    super.new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(c->members[0]->method, nullptr);
  EXPECT_EQ(c->members[0]->method->name, "new");
}

// class_constructor_declaration permits the super.new call to take the lone
// 'default' keyword in place of an argument list.
TEST(ClassItems, ConstructorSuperNewDefault) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "    super.new(default);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  ASSERT_NE(c->members[0]->method, nullptr);
  EXPECT_EQ(c->members[0]->method->name, "new");
}

// class_constructor_declaration permits the optional closing label, which the
// grammar restricts to 'endfunction : new'.
TEST(ClassItems, ConstructorEndLabel) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  ASSERT_NE(c->members[0]->method, nullptr);
  EXPECT_EQ(c->members[0]->method->name, "new");
}

// class_constructor_declaration's optional class_scope: an out-of-body
// constructor definition 'function ClassName :: new (...) ; ... endfunction'.
TEST(ClassItems, ClassConstructorClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern function new(int x);\n"
      "endclass\n"
      "function C::new(int x);\n"
      "endfunction\n");
  ASSERT_FALSE(r.has_errors);
  // The out-of-body definition lands among the compilation-unit items, carrying
  // both the qualifying class scope and the constructor name.
  const ModuleItem* def = nullptr;
  for (auto* it : r.cu->cu_items) {
    if (it->kind == ModuleItemKind::kFunctionDecl && it->name == "new") {
      def = it;
      break;
    }
  }
  ASSERT_NE(def, nullptr);
  EXPECT_EQ(def->method_class, "C");
}

// --- class_constructor_prototype ---------------------------------------------
// class_method's 'extern {method_qualifier} class_constructor_prototype' form:
//   class_constructor_prototype ::= function new [( [class_constructor_arg_list] )] ;
TEST(ClassItems, ClassConstructorPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern function new();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  ASSERT_NE(c->members[0]->method, nullptr);
  EXPECT_EQ(c->members[0]->method->name, "new");
  EXPECT_TRUE(c->members[0]->method->is_extern);
}

// --- class_constructor_arg_list / class_constructor_arg ----------------------
// class_constructor_arg_list ::= class_constructor_arg { , class_constructor_arg }
// class_constructor_arg ::= tf_port_item | default
// The constructor argument list accepts several ordinary port items together
// with the 'default' keyword argument.
TEST(ClassItems, ConstructorArgListWithDefaultArg) {
  auto r = Parse(
      "class C;\n"
      "  function new(int a, default, int b);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 1u);
  ASSERT_NE(c->members[0]->method, nullptr);
  ASSERT_EQ(c->members[0]->method->func_args.size(), 3u);
  EXPECT_EQ(c->members[0]->method->func_args[0].name, "a");
  EXPECT_TRUE(c->members[0]->method->func_args[1].is_default);
  EXPECT_EQ(c->members[0]->method->func_args[2].name, "b");
}

// --- interface_class_item / interface_class_method ---------------------------
// interface_class_method ::= pure virtual method_prototype ; inside an
// 'interface class' declaration.
TEST(ClassItems, InterfaceClassMethod) {
  auto r = Parse(
      "interface class I;\n"
      "  pure virtual function int f();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  EXPECT_TRUE(c->is_interface);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_TRUE(c->members[0]->is_pure_virtual);
  ASSERT_NE(c->members[0]->method, nullptr);
  EXPECT_EQ(c->members[0]->method->name, "f");
}

// interface_class_method also covers method_prototype's task_prototype branch:
// 'pure virtual task ... ;' inside an interface class.
TEST(ClassItems, InterfaceClassMethodTaskPrototype) {
  auto r = Parse(
      "interface class I;\n"
      "  pure virtual task t(int x);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  EXPECT_TRUE(c->is_interface);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_TRUE(c->members[0]->is_pure_virtual);
  ASSERT_NE(c->members[0]->method, nullptr);
  EXPECT_EQ(c->members[0]->method->name, "t");
}

// interface_class_item's type_declaration and parameter_declaration ';'
// alternatives are accepted inside an interface class body.
TEST(ClassItems, InterfaceClassItemTypeAndParameter) {
  auto r = Parse(
      "interface class I;\n"
      "  typedef int my_int;\n"
      "  parameter int P = 1;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  EXPECT_TRUE(c->is_interface);
  ASSERT_EQ(c->members.size(), 2u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kTypedef);
  EXPECT_EQ(c->members[1]->name, "P");
}

// interface_class_item's local_parameter_declaration ';' and empty ';'
// alternatives are accepted in an interface class body; the stray semicolon
// contributes no member.
TEST(ClassItems, InterfaceClassItemLocalParamAndEmpty) {
  auto r = Parse(
      "interface class I;\n"
      "  localparam int X = 1;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  EXPECT_TRUE(c->is_interface);
  ASSERT_EQ(c->members.size(), 1u);
  EXPECT_EQ(c->members[0]->name, "X");
}

// --- class_constraint --------------------------------------------------------
// class_constraint ::= constraint_prototype | constraint_declaration. A
// constraint with a block body is a declaration; one without is a prototype.
TEST(ClassItems, ClassConstraintDeclarationAndPrototype) {
  auto r = Parse(
      "class C;\n"
      "  constraint decl_c { x > 0; }\n"
      "  constraint proto_c;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 2u);
  EXPECT_EQ(c->members[0]->kind, ClassMemberKind::kConstraint);
  EXPECT_FALSE(c->members[0]->is_constraint_prototype);
  EXPECT_EQ(c->members[1]->kind, ClassMemberKind::kConstraint);
  EXPECT_TRUE(c->members[1]->is_constraint_prototype);
}

}  // namespace
