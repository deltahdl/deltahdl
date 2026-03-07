#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §8.21: Parse virtual class declaration.
TEST(Parser, VirtualClass) {
  auto r = Parse("virtual class base; endclass");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

// §8.21: Parse pure virtual function — is_pure_virtual flag.
TEST(ParserSection8, PureVirtualFunction) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 1u);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_virtual);
  EXPECT_TRUE(m->is_pure_virtual);
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
}

// §8.21: Parse pure virtual function with arguments.
TEST(ParserA26, FuncPrototypePureVirtual) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function int compute(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_pure_virtual);
}

// §8.21: Parse pure virtual task.
TEST(ParserA27, TaskPrototypePureVirtual) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual task do_work(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_pure_virtual);
}

// §8.21: Non-pure virtual method should not have is_pure_virtual set.
TEST(ParserSection8_21, NonPureVirtualNotFlagged) {
  auto r = Parse(
      "class Base;\n"
      "  virtual function void display(); endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_virtual);
  EXPECT_FALSE(m->is_pure_virtual);
}

// §8.21: Abstract class extending another abstract class with pure virtual.
TEST(ParserSection8_21, AbstractExtendsAbstract) {
  auto r = Parse(
      "virtual class Shape;\n"
      "  pure virtual function int area();\n"
      "endclass\n"
      "virtual class Shape2D extends Shape;\n"
      "  pure virtual function int perimeter();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
  EXPECT_TRUE(r.cu->classes[1]->is_virtual);
  EXPECT_TRUE(r.cu->classes[1]->members[0]->is_pure_virtual);
}

// §8.21: Concrete class overriding pure virtual with body.
TEST(ParserSection8_21, ConcreteOverridesPureVirtual) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  virtual function void display(); endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* derived_m = r.cu->classes[1]->members[0];
  EXPECT_TRUE(derived_m->is_virtual);
  EXPECT_FALSE(derived_m->is_pure_virtual);
}

}  // namespace
