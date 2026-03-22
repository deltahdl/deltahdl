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

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_SameTypeAssignOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  class K;\n"
             "    int id;\n"
             "  endclass\n"
             "  int aa[K];\n"
             "  int bb[K];\n"
             "  assign aa = bb;\n"
             "endmodule\n"));
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_DifferentTypeAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class A;\n"
      "    int id;\n"
      "  endclass\n"
      "  class B;\n"
      "    int id;\n"
      "  endclass\n"
      "  int aa[A];\n"
      "  int bb[B];\n"
      "  assign aa = bb;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_MixedTypeAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class K;\n"
      "    int id;\n"
      "  endclass\n"
      "  int aa[K];\n"
      "  int bb[int];\n"
      "  assign aa = bb;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
