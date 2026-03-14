#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassObjectParsing, StaticPropertyDeclaration) {
  auto r = Parse(
      "class Packet;\n"
      "  static integer fileID;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "fileID");
  EXPECT_TRUE(cls->members[0]->is_static);
}

TEST(ClassObjectParsing, StaticPropertyWithInitializer) {
  auto r = Parse(
      "class Packet;\n"
      "  static int count = 0;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_NE(cls->members[0]->init_expr, nullptr);
}

TEST(ClassObjectParsing, MixedStaticAndInstanceProperties) {
  auto r = Parse(
      "class C;\n"
      "  static int shared_val;\n"
      "  int inst_val;\n"
      "  static string name;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 3u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_EQ(cls->members[0]->name, "shared_val");
  EXPECT_FALSE(cls->members[1]->is_static);
  EXPECT_EQ(cls->members[1]->name, "inst_val");
  EXPECT_TRUE(cls->members[2]->is_static);
  EXPECT_EQ(cls->members[2]->name, "name");
}

TEST(ClassObjectParsing, StaticPropertyAccessViaInstance) {
  ParseOk(
      "class Packet;\n"
      "  static int fileID;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    automatic int c;\n"
      "    c = p.fileID;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ClassObjectParsing, StaticPropertyAccessViaScope) {
  ParseOk(
      "class Packet;\n"
      "  static int fileID;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int c;\n"
      "    c = Packet::fileID;\n"
      "  end\n"
      "endmodule\n");
}

}  // namespace
