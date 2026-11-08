#include <gtest/gtest.h>

#include <cstdint>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

const ClassDecl* FirstClass(const ParseResult& r) {
  return r.cu->classes.empty() ? nullptr : r.cu->classes[0];
}

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

TEST(ClassItems, ClassPropertyWrittenWithVar) {
  auto r = Parse(
      "class C;\n"
      "  var int x;\n"
      "  rand var bit [3:0] y;\n"
      "  var [7:0] z;\n"
      "  var signed s;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 4u);
  EXPECT_EQ(c->members[0]->name, "x");
  EXPECT_EQ(c->members[0]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(c->members[1]->name, "y");
  EXPECT_TRUE(c->members[1]->is_rand);
  EXPECT_EQ(c->members[1]->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(c->members[2]->name, "z");
  EXPECT_EQ(c->members[2]->data_type.kind, DataTypeKind::kImplicit);
  EXPECT_NE(c->members[2]->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(c->members[3]->name, "s");
  EXPECT_TRUE(c->members[3]->data_type.is_signed);
}

TEST(ClassItems, ClassPropertyOfImplicitTypeWithoutVarIsReported) {
  auto r = Parse(
      "class C;\n"
      "  z;\n"
      "  signed s;\n"
      "  const k = 1;\n"
      "  [7:0] w;\n"
      "endclass\n");
  for (uint32_t line : {2U, 3U, 4U, 5U}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "data_declaration without an explicit data type "
                              "requires the 'var' keyword",
                              line, "6.8"));
  }
}

TEST(ClassItems, ClassPropertyOfImplicitTypeWithVarStands) {
  auto r = Parse(
      "class C;\n"
      "  var z;\n"
      "  var signed s;\n"
      "  const int k = 1;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItems, ClassPropertyOfAnUnknownTypeNameDrawsNoVarReport) {
  auto r = Parse(
      "class C;\n"
      "  nosuch_t h;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got identifier", 2, "8.5"));
  for (const Diagnostic& d : r.diags) {
    EXPECT_FALSE(d.subclause == "6.8" && d.loc.column == 3) << d.message;
  }
}

TEST(ClassItems, ClassPropertyOfATypeReferenceAfterVarStands) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  var type(x) w;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 2u);
  EXPECT_EQ(c->members[1]->name, "w");
  EXPECT_NE(c->members[1]->data_type.type_ref_expr, nullptr);
}

TEST(ClassItems, ClassPropertyOfATypeReferenceWithoutVarIsReported) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  type(x) bad;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "type_reference in a variable declaration must be "
                            "preceded by the 'var' keyword",
                            3, "6.8"));
}

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

TEST(ClassItems, ClassConstructorClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern function new(int x);\n"
      "endclass\n"
      "function C::new(int x);\n"
      "endfunction\n");
  ASSERT_FALSE(r.has_errors);
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

TEST(ClassItems, MethodQualifierAdmitsNoRandomQualifierOrConst) {
  auto r = Parse(
      "class C;\n"
      "  rand function void f();\n"
      "  endfunction\n"
      "  const task t();\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, "'rand' is no qualifier of a class method",
                            2, "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'const' is no qualifier of a class method", 4, "A.1.9"));
}

TEST(ClassItems, PureWithoutVirtualIsRejected) {
  auto r = Parse(
      "class C;\n"
      "  pure function void f();\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'pure' qualifies 'virtual'; a method is pure virtual", 2,
      "A.1.9"));
}

TEST(ClassItems, PropertyQualifierAdmitsNoMethodQualifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual int x;\n"
      "  pure virtual int y;\n"
      "  extern int z;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'virtual' is no qualifier of a class property", 2, "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'pure' is no qualifier of a class property", 3, "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'extern' is no qualifier of a class property", 4, "A.1.9"));
}

TEST(ClassItems, PropertyQualifiersEachAdmitted) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  rand int a;\n"
              "  randc bit [1:0] b;\n"
              "  static int c;\n"
              "  protected int d;\n"
              "  local int e;\n"
              "  const static int f = 1;\n"
              "  static const int g = 2;\n"
              "endclass\n"));
}

TEST(ClassItems, ConstraintAdmitsNoPropertyOrMethodQualifier) {
  auto r = Parse(
      "class C;\n"
      "  rand constraint c1 { x > 0; }\n"
      "  protected constraint c2 { x > 0; }\n"
      "  virtual constraint c3;\n"
      "  static constraint c4 { x > 0; }\n"
      "  extern constraint c5;\n"
      "  pure constraint c6;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'rand' is no qualifier of a class constraint", 2, "A.1.9"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "'protected' is no qualifier of a class constraint",
                            3, "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'virtual' is no qualifier of a class constraint", 4, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, "is no qualifier of a class constraint",
                             5, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, "is no qualifier of a class constraint",
                             6, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, "is no qualifier of a class constraint",
                             7, "A.1.9"));
}

TEST(ClassItems, ParameterAndCovergroupAdmitNoQualifier) {
  auto r = Parse(
      "class C;\n"
      "  static parameter int W = 4;\n"
      "  local localparam int D = 2;\n"
      "  protected covergroup cg;\n"
      "  endgroup\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'static' is no qualifier of a parameter declaration", 2,
      "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'local' is no qualifier of a parameter declaration", 3,
      "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'protected' is no qualifier of a covergroup declaration", 4,
      "A.1.9"));
}

TEST(ClassItems, TypeDeclarationAdmitsNoMethodQualifierOrConst) {
  auto r = Parse(
      "class C;\n"
      "  virtual typedef int t1;\n"
      "  const typedef int t2;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'virtual' is no qualifier of a type declaration", 2, "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'const' is no qualifier of a type declaration", 3, "A.1.9"));
}

TEST(ClassItems, NestedVirtualClassKeepsItsVirtual) {
  auto r = Parse(
      "class C;\n"
      "  virtual class Inner;\n"
      "  endclass\n"
      "  static class Other;\n"
      "  endclass\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'static' is no qualifier of a nested class declaration", 4,
      "A.1.9"));
  const ClassDecl* c = FirstClass(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->members.size(), 2u);
  ASSERT_NE(c->members[0]->nested_class, nullptr);
  EXPECT_TRUE(c->members[0]->nested_class->is_virtual);
  ASSERT_NE(c->members[1]->nested_class, nullptr);
  EXPECT_FALSE(c->members[1]->nested_class->is_virtual);
}

TEST(ClassItems, ExternAfterAnotherQualifierIsError) {
  auto r = Parse(
      "class C;\n"
      "  local extern function void h();\n"
      "  virtual extern task t();\n"
      "  static extern function int s();\n"
      "  extern local function void k();\n"
      "  extern protected virtual function void v();\n"
      "endclass\n");
  const char* const kMsg = "'extern' is written after another qualifier";
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 2, "A.1.9"));
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 3, "A.1.9"));
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 4, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kMsg, 5, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kMsg, 6, "A.1.9"));
}

TEST(ClassItems, PureApartFromVirtualIsError) {
  auto r = Parse(
      "virtual class C;\n"
      "  virtual pure function void f();\n"
      "  pure local virtual task t();\n"
      "  protected pure virtual function void g();\n"
      "  pure virtual protected function void p();\n"
      "  extern protected pure virtual function void e();\n"
      "endclass\n");
  const char* const kApart = "'pure' is written apart from 'virtual'";
  const char* const kOpens = "a pure virtual method prototype opens with";
  EXPECT_TRUE(ReportedError(r.diags, kApart, 2, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kOpens, 2, "A.1.9"));
  EXPECT_TRUE(ReportedError(r.diags, kApart, 3, "A.1.9"));
  EXPECT_TRUE(ReportedError(r.diags, kOpens, 4, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kApart, 4, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kApart, 5, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kOpens, 5, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kApart, 6, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kOpens, 6, "A.1.9"));
}

TEST(ClassItems, PureVirtualWithABodyIsNotReportedForItsOrder) {
  auto r = Parse(
      "virtual class C;\n"
      "  protected pure virtual function void g();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, "a pure virtual method shall not have", 2,
                            "8.21"));
  EXPECT_FALSE(ReportedError(
      r.diags, "a pure virtual method prototype opens with", 2, "A.1.9"));
}

TEST(ClassItems, RandomQualifierAfterConstIsError) {
  auto r = Parse(
      "class C;\n"
      "  const rand int x = 1;\n"
      "  const static randc bit [3:0] y = 2;\n"
      "  rand const int z = 3;\n"
      "  static const int w = 4;\n"
      "endclass\n");
  const char* const kMsg = "a random qualifier is written after 'const'";
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 2, "A.1.9"));
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 3, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kMsg, 4, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kMsg, 5, "A.1.9"));
}

TEST(ClassItems, InterfaceClassItemQualifiersAreErrors) {
  auto r = Parse(
      "interface class I;\n"
      "  pure virtual protected function void f();\n"
      "  pure virtual local task t();\n"
      "  extern pure virtual function void g();\n"
      "  protected typedef int T;\n"
      "  rand typedef bit B;\n"
      "  pure virtual function void ok();\n"
      "  typedef int U;\n"
      "  localparam type L = int;\n"
      "  parameter int P = 1;\n"
      "endclass\n");
  const char* const kMethod = "is no qualifier of a method of an interface";
  const char* const kType =
      "is no qualifier of a type declaration in an interface";
  EXPECT_TRUE(ReportedError(
      r.diags, "'protected' is no qualifier of a method of an interface class",
      2, "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'local' is no qualifier of a method of an interface class", 3,
      "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'extern' is no qualifier of a method of an interface class", 4,
      "A.1.9"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "'protected' is no qualifier of a type declaration "
                            "in an interface class",
                            5, "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags,
      "'rand' is no qualifier of a type declaration in an interface class", 6,
      "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kMethod, 7, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, kType, 8, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, "is no qualifier", 9, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, "is no qualifier", 10, "A.1.9"));
}

TEST(ClassItems, OrdinaryClassItemsTakeTheseQualifiers) {
  EXPECT_TRUE(
      ParseOk("virtual class V;\n"
              "  pure virtual protected function void f();\n"
              "  pure virtual local task t();\n"
              "  extern pure virtual function void g();\n"
              "  protected typedef int T;\n"
              "  rand typedef bit B;\n"
              "endclass\n"));
}

TEST(ClassItems, DefaultArgumentOutsideConstructorIsRejected) {
  auto r = Parse(
      "class C;\n"
      "  function void f(int a, default);\n"
      "  endfunction\n"
      "  task t(default);\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a 'default' argument stands in a class constructor's argument list "
      "alone",
      2, "A.1.9"));
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a 'default' argument stands in a class constructor's argument list "
      "alone",
      4, "A.1.9"));
}

}  // namespace
