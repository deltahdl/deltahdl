#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kFerrorShape =
    "$ferror takes a file descriptor and a variable for the description";

std::string StatusIn(const std::string& call) {
  return "module t;\n"
         "  integer fd, e;\n"
         "  string msg;\n"
         "  initial e = " +
         call +
         ";\n"
         "endmodule\n";
}

void ExpectReported(const std::string& call) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(StatusIn(call), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFerrorShape, 4, "21.3.7"))
      << call;
}

TEST(FerrorArgumentList, DISABLED_NoArgumentIsReported) {
  ExpectReported("$ferror()");
}

TEST(FerrorArgumentList, DISABLED_ADescriptorAloneIsReported) {
  ExpectReported("$ferror(fd)");
}

TEST(FerrorArgumentList, DISABLED_ThreeArgumentsAreReported) {
  ExpectReported("$ferror(fd, msg, msg)");
}

TEST(FerrorArgumentList, DISABLED_AStringLiteralDestinationIsReported) {
  ExpectReported("$ferror(fd, \"lit\")");
}

TEST(FerrorArgumentList, DISABLED_AnExpressionDestinationIsReported) {
  ExpectReported("$ferror(fd, {msg, msg})");
}

TEST(FerrorArgumentList, DISABLED_ADescriptorAloneInAClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "class C;\n"
      "  function int f(integer fd); return $ferror(fd); endfunction\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFerrorShape, 2, "21.3.7"));
}

TEST(FerrorArgumentList, PackedAndStringDestinationsAreAccepted) {
  for (const char* decl : {"  reg [639:0] d;", "  string d;",
                           "  bit [1023:0] d;", "  logic [7:0] d;"}) {
    ElabFixture f;
    Elaborate(std::string("module t;\n  integer fd, e;\n") + decl +
                  "\n  initial e = $ferror(fd, d);\nendmodule\n",
              f);
    EXPECT_FALSE(f.has_errors) << decl;
  }
}

}  // namespace
