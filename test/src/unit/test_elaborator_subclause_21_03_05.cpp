#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string CallIn(const std::string& call) {
  return "module t;\n"
         "  integer fd, x, code;\n"
         "  initial code = " +
         call +
         ";\n"
         "endmodule\n";
}

void ExpectReported(const std::string& call, const std::string& message) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(CallIn(call), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, "21.3.5"))
      << call;
}

constexpr const char* kFtellShape = "$ftell takes one file descriptor";
constexpr const char* kFseekShape =
    "$fseek takes a file descriptor, an offset and an operation";
constexpr const char* kRewindShape = "$rewind takes one file descriptor";

TEST(FilePositioningArgumentLists, DISABLED_FtellWithNoArgumentIsReported) {
  ExpectReported("$ftell()", kFtellShape);
}

TEST(FilePositioningArgumentLists, DISABLED_FtellWithTwoArgumentsIsReported) {
  ExpectReported("$ftell(fd, x)", kFtellShape);
}

TEST(FilePositioningArgumentLists, DISABLED_FseekWithOneArgumentIsReported) {
  ExpectReported("$fseek(fd)", kFseekShape);
}

TEST(FilePositioningArgumentLists, DISABLED_FseekWithTwoArgumentsIsReported) {
  ExpectReported("$fseek(fd, 0)", kFseekShape);
}

TEST(FilePositioningArgumentLists, DISABLED_FseekWithFourArgumentsIsReported) {
  ExpectReported("$fseek(fd, 0, 0, x)", kFseekShape);
}

TEST(FilePositioningArgumentLists, DISABLED_RewindWithNoArgumentIsReported) {
  ExpectReported("$rewind()", kRewindShape);
}

TEST(FilePositioningArgumentLists, DISABLED_RewindWithTwoArgumentsIsReported) {
  ExpectReported("$rewind(fd, x)", kRewindShape);
}

TEST(FilePositioningArgumentLists,
     DISABLED_FtellWithNoArgumentInAClassIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "class C;\n"
      "  function int f(); return $ftell(); endfunction\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFtellShape, 2, "21.3.5"));
}

TEST(FilePositioningArgumentLists, EveryWellFormedCallIsAccepted) {
  for (const char* call : {"$ftell(fd)", "$fseek(fd, x, 2)", "$rewind(fd)"}) {
    ElabFixture f;
    Elaborate(CallIn(call), f);
    EXPECT_FALSE(f.has_errors) << call;
  }
}

}  // namespace
