// §8.23: Class scope resolution operator ::

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- class_scope ---
// class_type ::
TEST(ParserA221, ClassScope) {
  auto r = Parse(
      "class base_cls;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m; base_cls::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_item ::= { attribute_instance } class_declaration (nested class)
TEST(SourceText, ClassNestedClass) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int val;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_EQ(members[0]->nested_class->name, "Inner");
}

}  // namespace
