#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string CallIn(const std::string& call) {
  return "module t;\n"
         "  integer fd, c, code;\n"
         "  string s;\n"
         "  reg [31:0] v;\n"
         "  reg [7:0] mem [0:3];\n"
         "  initial code = " +
         call +
         ";\n"
         "endmodule\n";
}

void ExpectReported(const std::string& call, const std::string& message) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(CallIn(call), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 6, "21.3.4"))
      << call;
}

constexpr const char* kFgetcShape = "$fgetc takes one file descriptor";
constexpr const char* kUngetcShape =
    "$ungetc takes a character and a file descriptor";
constexpr const char* kFgetsShape =
    "$fgets takes a variable and a file descriptor";
constexpr const char* kFscanfShape =
    "$fscanf takes a file descriptor, a format and the variables it fills";
constexpr const char* kSscanfShape =
    "$sscanf takes a string, a format and the variables it fills";
constexpr const char* kFreadShape =
    "$fread takes a variable or a memory, a file descriptor, and for a memory "
    "an optional start and count";

TEST(FileReadArgumentLists, DISABLED_FgetcWithNoArgumentIsReported) {
  ExpectReported("$fgetc()", kFgetcShape);
}

TEST(FileReadArgumentLists, DISABLED_FgetcWithTwoArgumentsIsReported) {
  ExpectReported("$fgetc(fd, c)", kFgetcShape);
}

TEST(FileReadArgumentLists, DISABLED_UngetcWithOneArgumentIsReported) {
  ExpectReported("$ungetc(c)", kUngetcShape);
}

TEST(FileReadArgumentLists, DISABLED_UngetcWithThreeArgumentsIsReported) {
  ExpectReported("$ungetc(c, fd, c)", kUngetcShape);
}

TEST(FileReadArgumentLists, DISABLED_FgetsWithOneArgumentIsReported) {
  ExpectReported("$fgets(s)", kFgetsShape);
}

TEST(FileReadArgumentLists, DISABLED_FgetsWithThreeArgumentsIsReported) {
  ExpectReported("$fgets(s, fd, c)", kFgetsShape);
}

TEST(FileReadArgumentLists, DISABLED_FscanfWithNoFormatIsReported) {
  ExpectReported("$fscanf(fd)", kFscanfShape);
}

TEST(FileReadArgumentLists, DISABLED_SscanfWithNoFormatIsReported) {
  ExpectReported("$sscanf(s)", kSscanfShape);
}

TEST(FileReadArgumentLists, DISABLED_FreadWithNoDescriptorIsReported) {
  ExpectReported("$fread(v)", kFreadShape);
}

TEST(FileReadArgumentLists, DISABLED_FreadWithFiveArgumentsIsReported) {
  ExpectReported("$fread(mem, fd, 0, 2, c)", kFreadShape);
}

TEST(FileReadArgumentLists, DISABLED_FgetsIntoAConstantIsReported) {
  ExpectReported("$fgets(5, fd)",
                 "the destination of $fgets must be a variable");
}

TEST(FileReadArgumentLists, DISABLED_FgetsIntoAnOperatorExpressionIsReported) {
  ExpectReported("$fgets(v + c, fd)",
                 "the destination of $fgets must be a variable");
}

TEST(FileReadArgumentLists, DISABLED_FreadIntoAConstantIsReported) {
  ExpectReported("$fread(5, fd)",
                 "the destination of $fread must be a variable or a memory");
}

TEST(FileReadArgumentLists, EveryFormOfSyntaxIsAccepted) {
  for (const char* call :
       {"$fgetc(fd)", "$ungetc(c, fd)", "$fgets(s, fd)", "$fgets(v, fd)",
        "$fscanf(fd, \"%d\", c)", "$fscanf(fd, \"%d %d\", c, v)",
        "$sscanf(s, \"%d\", c)", "$fread(v, fd)", "$fread(mem, fd)",
        "$fread(mem, fd, 1)", "$fread(mem, fd, 1, 2)", "$fread(mem, fd, , 2)",
        "$fread(mem[1], fd)"}) {
    ElabFixture f;
    Elaborate(CallIn(call), f);
    EXPECT_FALSE(f.has_errors) << call;
  }
}

}  // namespace
