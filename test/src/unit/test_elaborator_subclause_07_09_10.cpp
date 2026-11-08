#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array index type mismatch in argument",
                            7, "7.9.10"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 7, "7.9.10"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array index type mismatch in argument",
                            7, "7.9.10"));
}

TEST(Elaboration, AssocArgElementTypeMismatchInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial fork\n"
      "    f(aa);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 7, "7.9.10"));
}

TEST(Elaboration, AssocArgElementTypeMismatchInAssertionPassStmtRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial assert (1) f(aa);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 6, "7.9.10"));
}

TEST(Elaboration, AssocArgElementTypeMismatchInAssertionFailStmtRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial assert (1) else f(aa);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 6, "7.9.10"));
}

TEST(Elaboration, AssocArgElementTypeMismatchInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial randcase\n"
      "    1 : f(aa);\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 7, "7.9.10"));
}

TEST(Elaboration, AssocArgElementTypeMismatchInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { f(aa); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 8, "7.9.10"));
}

TEST(Elaboration,
     AssocArgElementTypeMismatchInRandsequenceWeightCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int i;\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { f(aa); };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 9, "7.9.10"));
}

}  // namespace
