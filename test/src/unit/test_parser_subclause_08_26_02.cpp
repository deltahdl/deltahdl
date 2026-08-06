#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ExtendsVsImplementsParsing, InterfaceClassExtendsMultiple) {
  auto r = Parse(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "interface class C extends A, B;\n"
      "  pure virtual function void fc();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 3u);
  EXPECT_EQ(r.cu->classes[2]->name, "C");
  EXPECT_EQ(r.cu->classes[2]->base_class, "A");
}

TEST(ExtendsVsImplementsParsing, ImplementsMultipleInterfaces) {
  auto r = Parse(
      "class C implements IFace1, IFace2, IFace3;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->implements_types.size(), 3u);
  EXPECT_EQ(cls->implements_types[0].name, "IFace1");
  EXPECT_EQ(cls->implements_types[1].name, "IFace2");
  EXPECT_EQ(cls->implements_types[2].name, "IFace3");
}

TEST(ExtendsVsImplementsParsing, ImplementsWithParamAssignment) {
  auto r = Parse(
      "class C implements IFace#(int);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->implements_types.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->implements_types[0].name, "IFace");
}

TEST(ExtendsVsImplementsParsing, ImplementsSingleInterface) {
  auto r = Parse(
      "class C implements IFace;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->implements_types.size(), 1u);
  EXPECT_EQ(cls->implements_types[0].name, "IFace");
}

TEST(ExtendsVsImplementsParsing, ExtendsAndImplementsCombined) {
  auto r = Parse(
      "interface class IA; endclass\n"
      "class Base; endclass\n"
      "class C extends Base implements IA;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[2];
  EXPECT_EQ(cls->base_class, "Base");
  ASSERT_EQ(cls->implements_types.size(), 1u);
  EXPECT_EQ(cls->implements_types[0].name, "IA");
}

TEST(ExtendsVsImplementsParsing, VirtualClassImplementsInterface) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "virtual class VC implements IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  EXPECT_TRUE(cls->is_virtual);
  ASSERT_EQ(cls->implements_types.size(), 1u);
  EXPECT_EQ(cls->implements_types[0].name, "IC");
}

TEST(ExtendsVsImplementsParsing, InterfaceClassNoExtends) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_TRUE(cls->is_interface);
  EXPECT_TRUE(cls->base_class.empty());
  EXPECT_TRUE(cls->extends_interfaces.empty());
  EXPECT_TRUE(cls->implements_types.empty());
}

}  // namespace
