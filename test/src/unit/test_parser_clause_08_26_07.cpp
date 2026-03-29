#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(InterfaceClassPartialImplementationParsing,
     VirtualClassWithMixedMethodsAst) {
  auto r = Parse(
      "interface class IntfClass;\n"
      "  pure virtual function bit funcA();\n"
      "  pure virtual function bit funcB();\n"
      "endclass\n"
      "virtual class ClassA implements IntfClass;\n"
      "  virtual function bit funcA();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  pure virtual function bit funcB();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);

  auto* intf = r.cu->classes[0];
  EXPECT_TRUE(intf->is_interface);
  EXPECT_EQ(intf->name, "IntfClass");

  auto* cls = r.cu->classes[1];
  EXPECT_TRUE(cls->is_virtual);
  EXPECT_FALSE(cls->is_interface);
  ASSERT_EQ(cls->implements_types.size(), 1u);
  EXPECT_EQ(cls->implements_types[0], "IntfClass");

  ASSERT_EQ(cls->members.size(), 2u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(cls->members[0]->is_virtual);
  EXPECT_FALSE(cls->members[0]->is_pure_virtual);
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(cls->members[1]->is_pure_virtual);
}

TEST(InterfaceClassPartialImplementationParsing,
     ConcreteClassExtendsPartialVirtualAst) {
  auto r = Parse(
      "interface class IntfClass;\n"
      "  pure virtual function bit funcA();\n"
      "  pure virtual function bit funcB();\n"
      "endclass\n"
      "virtual class ClassA implements IntfClass;\n"
      "  virtual function bit funcA();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  pure virtual function bit funcB();\n"
      "endclass\n"
      "class ClassB extends ClassA;\n"
      "  virtual function bit funcB();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 3u);

  auto* concrete = r.cu->classes[2];
  EXPECT_FALSE(concrete->is_virtual);
  EXPECT_FALSE(concrete->is_interface);
  EXPECT_EQ(concrete->base_class, "ClassA");
  ASSERT_EQ(concrete->members.size(), 1u);
  EXPECT_EQ(concrete->members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(concrete->members[0]->is_virtual);
  EXPECT_FALSE(concrete->members[0]->is_pure_virtual);
}

}  // namespace
