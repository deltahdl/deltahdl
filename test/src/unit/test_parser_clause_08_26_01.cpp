#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, InterfaceClassItems) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void do_thing();\n"
      "  pure virtual task do_task();\n"
      "  typedef int my_int;\n"
      "  localparam int LP = 5;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(members[0]->is_virtual);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kTypedef);
  EXPECT_EQ(members[3]->kind, ClassMemberKind::kProperty);
}

TEST(SourceText, InterfaceClassDecl) {
  auto r = Parse("interface class IC; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "IC");
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
