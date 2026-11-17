#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kFflushShape =
    "$fflush takes at most one multichannel or file descriptor";

std::string FlushIn(const std::string& call) {
  return "module t;\n"
         "  integer fd, mcd;\n"
         "  initial " +
         call +
         ";\n"
         "endmodule\n";
}

void ExpectReported(const std::string& call) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(FlushIn(call), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFflushShape, 3, "21.3.6"))
      << call;
}

TEST(FlushArgumentList, DISABLED_TwoDescriptorsAreReported) {
  ExpectReported("$fflush(fd, fd)");
}

TEST(FlushArgumentList, DISABLED_AnMcdAndAFdAreReported) {
  ExpectReported("$fflush(mcd, fd)");
}

TEST(FlushArgumentList, DISABLED_ThreeArgumentsAreReported) {
  ExpectReported("$fflush(fd, mcd, fd)");
}

TEST(FlushArgumentList, DISABLED_TwoArgumentsInAClassMethodAreReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "class C;\n"
      "  function void f(integer fd); $fflush(fd, fd); endfunction\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFflushShape, 2, "21.3.6"));
}

TEST(FlushArgumentList, NoArgumentAndOneDescriptorAreAccepted) {
  for (const char* call :
       {"$fflush()", "$fflush(fd)", "$fflush(mcd)", "$fflush(mcd | 1)"}) {
    ElabFixture f;
    Elaborate(FlushIn(call), f);
    EXPECT_FALSE(f.has_errors) << call;
  }
}

}  // namespace
