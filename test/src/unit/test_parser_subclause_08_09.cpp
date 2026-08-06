#include "fixture_parser.h"

using namespace delta;

namespace {

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

TEST(ClassObjectParsing, MultipleStaticDeclaratorsOnOneLine) {
  auto r = Parse(
      "class C;\n"
      "  static int a, b;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 2u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_EQ(cls->members[0]->name, "a");
  EXPECT_TRUE(cls->members[1]->is_static);
  EXPECT_EQ(cls->members[1]->name, "b");
}

TEST(ClassObjectParsing, StaticPropertyWriteViaInstance) {
  ParseOk(
      "class C;\n"
      "  static int count;\n"
      "endclass\n"
      "module m;\n"
      "  C c1;\n"
      "  initial begin\n"
      "    c1 = new;\n"
      "    c1.count = 5;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ClassObjectParsing, StaticPropertyWriteViaScope) {
  ParseOk(
      "class C;\n"
      "  static int count;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C::count = 10;\n"
      "  end\n"
      "endmodule\n");
}

// §8.9 C1 admits the static qualifier on a property of any data type (§8.5).
// A packed-vector declarator exercises a different parse path (packed
// dimensions) than the scalar forms above; the qualifier is still recorded.
TEST(ClassObjectParsing, StaticPackedVectorProperty) {
  auto r = Parse(
      "class C;\n"
      "  static bit [7:0] flags;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_EQ(cls->members[0]->name, "flags");
}

// §8.9 C1 with a real-typed property: the real keyword is a distinct parse
// path from the integral forms, and the static qualifier is still recorded.
TEST(ClassObjectParsing, StaticRealProperty) {
  auto r = Parse(
      "class C;\n"
      "  static real r;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_EQ(cls->members[0]->name, "r");
}

}  // namespace
