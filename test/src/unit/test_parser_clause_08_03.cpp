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

TEST(ParserSection8, EmptyClassDecl) {
  auto r = Parse("class Packet; endclass");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_TRUE(r.cu->classes[0]->members.empty());
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

// --- §8.3 dynamic_override_specifiers on methods ---
TEST(ParserClause08_03, MethodInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :initial void foo(); endfunction\n"
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
