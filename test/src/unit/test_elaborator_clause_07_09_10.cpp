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

TEST(Elaboration, AssocArgElementTypeMismatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
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

// Compatible-type acceptance is not limited to an int element: a packed-vector
// element that matches between actual and formal (same width, same
// 4-state-ness) binds cleanly. Exercises the element-equivalence accept path
// for a non-int value type.
TEST(Elaboration, AssocArgPackedElementSameTypeOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  logic [7:0] aa[int];\n"
             "  function automatic logic [7:0] f(logic [7:0] x[int]);\n"
             "    return x[0];\n"
             "  endfunction\n"
             "  initial begin\n"
             "    aa[0] = 8'hAB;\n"
             "    f(aa);\n"
             "  end\n"
             "endmodule\n"));
}

// A queue is another array kind: it cannot be passed where an associative
// formal is expected, just like the fixed-size and dynamic cases.
TEST(Elaboration, QueueToAssocArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int q[$];\n"
      "  function automatic int g(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    g(q);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The reverse also holds: an associative array cannot be passed where a queue
// formal (another array kind) is expected.
TEST(Elaboration, AssocArgToQueueRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int g(int x[$]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    g(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The index-type compatibility rule still applies when the actual reaches the
// formal through a named argument binding rather than a positional one: a
// string-indexed actual bound by name to an int-indexed formal is rejected.
TEST(Elaboration, AssocArgIndexMismatchViaNamedBindingRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[string];\n"
      "  function automatic int f(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(.x(aa));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
