#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FileOpenCloseElaboration, DISABLED_FopenWithNoArgumentIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  integer fd;\n"
      "  initial fd = $fopen();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$fopen takes a filename and an optional type", 4,
                            "21.3.1"));
}

TEST(FileOpenCloseElaboration, DISABLED_FopenWithThreeArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  integer fd;\n"
      "  initial fd = $fopen(\"f.txt\", \"r\", 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$fopen takes a filename and an optional type", 4,
                            "21.3.1"));
}

TEST(FileOpenCloseElaboration, FopenWithAFilenameOrAFilenameAndTypeIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin fd = $fopen(\"f.txt\"); fd = $fopen(\"f.txt\", \"r\"); "
      "end;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(FileOpenCloseElaboration, DISABLED_FcloseWithNoArgumentIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  integer fd;\n"
      "  initial $fclose();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$fclose takes one descriptor", 4, "21.3.1"));
}

TEST(FileOpenCloseElaboration, DISABLED_FcloseWithTwoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  integer fd;\n"
      "  initial $fclose(fd, fd);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$fclose takes one descriptor", 4, "21.3.1"));
}

TEST(FileOpenCloseElaboration, FcloseWithOneDescriptorIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  integer fd;\n"
      "  initial $fclose(fd);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(FileOpenCloseElaboration, DISABLED_ARealFilenameIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  real r = 1.5;\n"
      "  integer fd;\n"
      "  initial fd = $fopen(r, \"w\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the filename argument of $fopen must be a string literal, "
                    "a string or an integral value holding a character string",
                    4, "21.3.1"));
}

TEST(FileOpenCloseElaboration, DISABLED_AnUnpackedIntArrayFilenameIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  int u[2] = '{1, 2};\n"
      "  integer fd;\n"
      "  initial fd = $fopen(u);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the filename argument of $fopen must be a string literal, "
                    "a string or an integral value holding a character string",
                    4, "21.3.1"));
}

TEST(FileOpenCloseElaboration,
     AStringLiteralStringOrIntegralFilenameIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  string s = \"a.txt\";\n"
      "  bit [39:0] b = \"b.txt\";\n"
      "  integer fd;\n"
      "  initial begin fd = $fopen(\"c.txt\", \"w\"); fd = $fopen(s, \"w\"); "
      "fd = $fopen(b); end;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(FileOpenCloseElaboration, DISABLED_TheTypeLiteralXIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  integer fd;\n"
      "  initial fd = $fopen(\"f.txt\", \"x\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the type argument of $fopen does not name a way to open a file", 4,
      "21.3.1"));
}

TEST(FileOpenCloseElaboration, DISABLED_TheTypeLiteralRwIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  integer fd;\n"
      "  initial fd = $fopen(\"f.txt\", \"rw\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the type argument of $fopen does not name a way to open a file", 4,
      "21.3.1"));
}

TEST(FileOpenCloseElaboration, DISABLED_TheTypeLiteralWxIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  integer fd;\n"
      "  initial fd = $fopen(\"f.txt\", \"wx\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the type argument of $fopen does not name a way to open a file", 4,
      "21.3.1"));
}

TEST(FileOpenCloseElaboration, DISABLED_TheTypeLiteralEmptyIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  integer fd;\n"
      "  initial fd = $fopen(\"f.txt\", \"\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the type argument of $fopen does not name a way to open a file", 4,
      "21.3.1"));
}

TEST(FileOpenCloseElaboration, EveryTableTypeLiteralIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin fd = $fopen(\"f.txt\", \"r\"); fd = $fopen(\"f.txt\", "
      "\"rb\"); fd = $fopen(\"f.txt\", \"w\"); fd = $fopen(\"f.txt\", \"wb\"); "
      "fd = $fopen(\"f.txt\", \"a\"); fd = $fopen(\"f.txt\", \"ab\"); fd = "
      "$fopen(\"f.txt\", \"r+\"); fd = $fopen(\"f.txt\", \"r+b\"); fd = "
      "$fopen(\"f.txt\", \"rb+\"); fd = $fopen(\"f.txt\", \"w+\"); fd = "
      "$fopen(\"f.txt\", \"w+b\"); fd = $fopen(\"f.txt\", \"wb+\"); fd = "
      "$fopen(\"f.txt\", \"a+\"); fd = $fopen(\"f.txt\", \"a+b\"); fd = "
      "$fopen(\"f.txt\", \"ab+\"); end;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
