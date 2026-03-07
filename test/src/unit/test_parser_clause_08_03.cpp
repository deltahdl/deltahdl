// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, DescriptionClass) {
  auto r = Parse("class C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

TEST(ParserSection8, ClassWithLifetime) {
  auto r = Parse(
      "class automatic MyClass;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "MyClass");
}

TEST(ParserSection23, EndLabelClass) {
  auto r = Parse("class myclass; endclass : myclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1);
  EXPECT_EQ(r.cu->classes[0]->name, "myclass");
}

TEST(Parser, EmptyClass) {
  auto r = Parse("class empty_cls; endclass");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1);
  EXPECT_EQ(r.cu->classes[0]->name, "empty_cls");
  EXPECT_FALSE(r.cu->classes[0]->is_virtual);
}

TEST(SourceText, ClassParameters) {
  auto r = Parse(
      "class C;\n"
      "  localparam int LP = 10;\n"
      "  parameter int P = 20;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kProperty);
}

TEST(SourceText, ClassEmptyItem) {
  auto r = Parse(
      "class C;\n"
      "  ;\n"
      "  int x;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);

  EXPECT_EQ(r.cu->classes[0]->members.size(), 1u);
}

TEST(SourceText, ClassEndLabel) {
  auto r = Parse("class C; endclass : C\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SourceText, ClassPropertyWithQualifiers) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  randc bit [3:0] y;\n"
      "  static int count;\n"
      "  protected int secret;\n"
      "  local int hidden;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 5u);
  EXPECT_TRUE(members[0]->is_rand);
  EXPECT_EQ(members[0]->name, "x");
  EXPECT_TRUE(members[1]->is_randc);
  EXPECT_EQ(members[1]->name, "y");
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[3]->is_protected);
  EXPECT_TRUE(members[4]->is_local);
}

TEST(SourceText, ClassQualifierCombinations) {
  auto r = Parse(
      "class C;\n"
      "  static local int a;\n"
      "  protected rand int b;\n"
      "  static virtual function void sv_fn(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_TRUE(members[0]->is_static);
  EXPECT_TRUE(members[0]->is_local);
  EXPECT_TRUE(members[1]->is_protected);
  EXPECT_TRUE(members[1]->is_rand);
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[2]->is_virtual);
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

TEST(ParserSection8, EmptyClassDecl) {
  auto r = Parse("class Packet; endclass");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_TRUE(r.cu->classes[0]->members.empty());
}

TEST(ParserSection6, ClassVarDecl_ClassParsed) {
  auto r = Parse(
      "class MyClass;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  MyClass obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->classes.empty());
  EXPECT_EQ(r.cu->classes[0]->name, "MyClass");
  ASSERT_FALSE(r.cu->modules.empty());
}

// --- §8.3 implements clause ---
TEST(ParserClause08_03, ImplementsSingleInterface) {
  auto r = Parse(
      "class C implements IFace;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->implements_types.size(), 1u);
  EXPECT_EQ(cls->implements_types[0], "IFace");
}

TEST(ParserClause08_03, ImplementsMultipleInterfaces) {
  auto r = Parse(
      "class C implements IFace1, IFace2, IFace3;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->implements_types.size(), 3u);
  EXPECT_EQ(cls->implements_types[0], "IFace1");
  EXPECT_EQ(cls->implements_types[1], "IFace2");
  EXPECT_EQ(cls->implements_types[2], "IFace3");
}

TEST(ParserClause08_03, ExtendsAndImplements) {
  auto r = Parse(
      "class D extends Base implements IFace1, IFace2;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->base_class, "Base");
  ASSERT_EQ(cls->implements_types.size(), 2u);
  EXPECT_EQ(cls->implements_types[0], "IFace1");
  EXPECT_EQ(cls->implements_types[1], "IFace2");
}

TEST(ParserClause08_03, ImplementsWithParamAssignment) {
  auto r = Parse(
      "class C implements IFace#(int);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->implements_types.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->implements_types[0], "IFace");
}

// --- §8.3 extends with constructor arguments ---
TEST(ParserClause08_03, ExtendsWithArgs) {
  auto r = Parse(
      "class D extends Base(5);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->base_class, "Base");
  ASSERT_EQ(cls->extends_args.size(), 1u);
}

TEST(ParserClause08_03, ExtendsWithDefault) {
  auto r = Parse(
      "class D extends Base(default);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->base_class, "Base");
  EXPECT_TRUE(cls->extends_has_default);
}

// --- §8.3 class_constructor_arg: default keyword ---
TEST(ParserClause08_03, ConstructorDefaultArg) {
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

TEST(ParserClause08_03, ConstructorMixedArgsWithDefault) {
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

TEST(ParserClause08_03, ConstructorDefaultBeforeArgs) {
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

// --- §8.3 extern constructor prototype ---
TEST(ParserClause08_03, ExternConstructorPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern function new(int x);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[0]->method->name, "new");
}

// --- §8.3 dynamic_override_specifiers on methods ---
TEST(ParserClause08_03, MethodInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :initial void foo(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(ParserClause08_03, MethodExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :extends void bar(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(ParserClause08_03, MethodFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :final void baz(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(ParserClause08_03, MethodInitialFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  function :initial :final void qux(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(ParserClause08_03, TaskDynamicOverrideSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  task :extends my_task(); endtask\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

// --- §8.3 footnote 9: default at most once in constructor arg list ---
TEST(ParserClause08_03, ErrorDuplicateDefaultInConstructorArgs) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(default, int x, default);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// --- §8.3 footnote 10: qualifier conflict errors ---
TEST(ParserClause08_03, ErrorBothLocalAndProtected) {
  auto r = Parse(
      "class C;\n"
      "  local protected int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause08_03, ErrorBothRandAndRandc) {
  auto r = Parse(
      "class C;\n"
      "  rand randc int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause08_03, ErrorDuplicateStatic) {
  auto r = Parse(
      "class C;\n"
      "  static static int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause08_03, ErrorDuplicateVirtual) {
  auto r = Parse(
      "class C;\n"
      "  virtual virtual function void f(); endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// --- §8.3 interface class extends multiple bases (§8.26) ---
TEST(ParserClause08_03, InterfaceClassExtendsMultiple) {
  auto r = Parse(
      "interface class IFace extends IBase1, IBase2;\n"
      "  pure virtual function void do_something();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  EXPECT_EQ(r.cu->classes[0]->base_class, "IBase1");
}

}  // namespace
