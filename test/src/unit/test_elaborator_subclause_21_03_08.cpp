#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kFeofShape = "$feof takes one file descriptor";

std::string EofIn(const std::string& call) {
  return "module t;\n"
         "  integer fd, e;\n"
         "  initial e = " +
         call +
         ";\n"
         "endmodule\n";
}

void ExpectReported(const std::string& call) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(EofIn(call), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFeofShape, 3, "21.3.8"))
      << call;
}

TEST(FeofArgumentList, DISABLED_NoArgumentIsReported) {
  ExpectReported("$feof()");
}

TEST(FeofArgumentList, DISABLED_TwoArgumentsAreReported) {
  ExpectReported("$feof(fd, fd)");
}

TEST(FeofArgumentList, DISABLED_ThreeArgumentsAreReported) {
  ExpectReported("$feof(fd, fd, fd)");
}

TEST(FeofArgumentList, DISABLED_NoArgumentInAClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "class C;\n"
      "  function int f(); return $feof(); endfunction\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFeofShape, 2, "21.3.8"));
}

TEST(FeofArgumentList, OneDescriptorIsAccepted) {
  for (const char* call :
       {"$feof(fd)", "$feof(fd + 0)", "$feof($fopen(\"x.txt\", \"r\"))"}) {
    ElabFixture f;
    Elaborate(EofIn(call), f);
    EXPECT_FALSE(f.has_errors) << call;
  }
}

}  // namespace
