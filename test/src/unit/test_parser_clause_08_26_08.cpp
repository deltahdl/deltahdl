#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassSyntaxParsing, InterfaceMethodDefaultArgs) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
              "  pure virtual function void foo(int a = 5);\n"
              "endclass\n"));
}

TEST(ClassSyntaxParsing, InterfaceMethodMultipleDefaultArgs) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
              "  pure virtual function int calc(int a = 0, int b = 1);\n"
              "endclass\n"));
}

TEST(ClassSyntaxParsing, InterfaceMethodDefaultArgAst) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void foo(int a = 5);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* intf = r.cu->classes[0];
  EXPECT_TRUE(intf->is_interface);
  ASSERT_EQ(intf->members.size(), 1u);
  auto* method = intf->members[0]->method;
  ASSERT_NE(method, nullptr);
  ASSERT_EQ(method->func_args.size(), 1u);
  EXPECT_EQ(method->func_args[0].name, "a");
  EXPECT_NE(method->func_args[0].default_value, nullptr);
}

TEST(ClassSyntaxParsing, InterfaceMethodMixedDefaultAndNonDefaultArgs) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function int calc(int a, int b = 1);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* method = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(method, nullptr);
  ASSERT_EQ(method->func_args.size(), 2u);
  EXPECT_EQ(method->func_args[0].default_value, nullptr);
  EXPECT_NE(method->func_args[1].default_value, nullptr);
}

TEST(ClassSyntaxParsing, InterfaceMethodNoDefaultArgs) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void foo(int a);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto* method = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(method, nullptr);
  ASSERT_EQ(method->func_args.size(), 1u);
  EXPECT_EQ(method->func_args[0].default_value, nullptr);
}

}  // namespace
