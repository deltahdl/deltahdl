#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_IsAssoc) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "data") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_IsClassIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Bar;\n"
      "    int x;\n"
      "  endclass\n"
      "  int aa[Bar];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_class_index);
      EXPECT_EQ(v.assoc_index_class_name, "Bar");
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_IndexWidth64) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class MyKey;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[MyKey];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "data") {
      EXPECT_EQ(v.assoc_index_width, 64u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_NotStringIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class C;\n"
      "    int x;\n"
      "  endclass\n"
      "  int aa[C];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_FALSE(v.is_string_index);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_LiteralIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  initial data[7] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_WrongClassHandleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  class Bar;\n"
      "    int x;\n"
      "  endclass\n"
      "  Bar b;\n"
      "  int data[Foo];\n"
      "  initial data[b] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_MatchingHandleNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  Foo k;\n"
      "  int data[Foo];\n"
      "  initial data[k] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_NullIndexNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  initial data[null] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A handle of a class derived from the index class is an accepted index.
TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_DerivedHandleNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Base;\n"
      "    int id;\n"
      "  endclass\n"
      "  class Derived extends Base;\n"
      "    int extra;\n"
      "  endclass\n"
      "  Derived d;\n"
      "  int data[Base];\n"
      "  initial data[d] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
