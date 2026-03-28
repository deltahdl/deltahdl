#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, AssocArgSameTypeOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  int aa[string];\n"
             "  function automatic int f(int x[string]);\n"
             "    return x[\"a\"];\n"
             "  endfunction\n"
             "  initial begin\n"
             "    aa[\"a\"] = 1;\n"
             "    f(aa);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(Elaboration, AssocArgIndexTypeMismatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[string];\n"
      "  function automatic int f(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(Elaboration, FixedArrayToAssocArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int fa[4];\n"
      "  function automatic int f(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(fa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(Elaboration, DynamicArrayToAssocArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int da[];\n"
      "  function automatic int f(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(da);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(Elaboration, AssocArgToFixedArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(int x[4]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(Elaboration, AssocArgToDynamicArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(int x[]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(Elaboration, AssocArgIntIndexOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  int aa[int];\n"
             "  function automatic int f(int x[int]);\n"
             "    return x[0];\n"
             "  endfunction\n"
             "  initial begin\n"
             "    f(aa);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
