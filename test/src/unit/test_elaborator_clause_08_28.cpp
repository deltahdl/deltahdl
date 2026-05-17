#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassesAndStructures, StructUsableWithoutNew) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef struct { int x; int y; } point_t;\n"
             "  point_t p;\n"
             "  initial begin\n"
             "    p.x = 1;\n"
             "    p.y = 2;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassesAndStructures, ClassDeclarationDoesNotCreateObject) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  C obj;\n"
             "  initial begin\n"
             "    obj = new;\n"
             "    obj.x = 5;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassesAndStructures, CastClassHandleToIntError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C obj;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    obj = new;\n"
      "    x = int'(obj);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ClassesAndStructures, CastClassHandleToLogicError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C obj;\n"
      "  initial begin\n"
      "    automatic logic [31:0] v;\n"
      "    obj = new;\n"
      "    v = logic'(obj);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ClassesAndStructures, ClassHandleAssignToIntError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C obj;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    obj = new;\n"
      "    x = obj;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ClassesAndStructures, IntAssignToClassHandleError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C obj;\n"
      "  initial begin\n"
      "    obj = 42;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ClassesAndStructures, CastIntToClassHandleError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C obj;\n"
      "  initial begin\n"
      "    obj = C'(42);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}
