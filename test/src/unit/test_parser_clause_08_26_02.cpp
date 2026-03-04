#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, ClassWithImplements) {
  auto r = Parse("class C implements I; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

TEST(ParserSection8, ClassImplementsMultipleInterfaces) {
  EXPECT_TRUE(
      ParseOk("interface class A;\n"
              "  pure virtual function void fa();\n"
              "endclass\n"
              "interface class B;\n"
              "  pure virtual function void fb();\n"
              "endclass\n"
              "class C implements A, B;\n"
              "  virtual function void fa();\n"
              "  endfunction\n"
              "  virtual function void fb();\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ParserSection8, ClassImplementsInterface) {
  auto r = Parse(
      "interface class PutIf;\n"
      "  pure virtual function void put(int a);\n"
      "endclass\n"
      "class Fifo implements PutIf;\n"
      "  virtual function void put(int a);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->name, "Fifo");
}

TEST(ParserSection8, InterfaceClassExtendsMultiple) {
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

TEST(ParserSection8, ExtendsAndImplements) {
  auto r = Parse(
      "interface class Iface;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class Base;\n"
      "endclass\n"
      "class Child extends Base implements Iface;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 3u);
  EXPECT_EQ(r.cu->classes[2]->base_class, "Base");
}

}
