// §8.26.2: Extends versus implements

#include "fixture_parser.h"

using namespace delta;

namespace {

// Class with implements clause.
TEST(SourceText, ClassWithImplements) {
  auto r = Parse("class C implements I; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

// Class implementing multiple interface classes.
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

}  // namespace
