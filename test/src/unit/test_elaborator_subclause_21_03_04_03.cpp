#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kStrKinds =
    "the str argument of $sscanf must be an integral, string or unpacked byte "
    "array value";

std::string ScanFrom(const std::string& decl) {
  return "module t;\n" + decl +
         "\n"
         "  integer n, v;\n"
         "  initial n = $sscanf(src, \"%d\", v);\n"
         "endmodule\n";
}

void ExpectSourceReported(const std::string& decl) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(ScanFrom(decl), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kStrKinds, 4, "21.3.4.3"))
      << decl;
}

TEST(SscanfSource, DISABLED_ARealSourceIsReported) {
  ExpectSourceReported("  real src;");
}

TEST(SscanfSource, DISABLED_AShortrealSourceIsReported) {
  ExpectSourceReported("  shortreal src;");
}

TEST(SscanfSource, DISABLED_AnUnpackedIntArraySourceIsReported) {
  ExpectSourceReported("  int src [4];");
}

TEST(SscanfSource, DISABLED_AnUnpackedStructSourceIsReported) {
  ExpectSourceReported("  struct { byte a; byte b; } src;");
}

TEST(SscanfSource, DISABLED_AnUnpackedUnionSourceIsReported) {
  ExpectSourceReported("  union { byte a; int b; } src;");
}

TEST(SscanfSource, DISABLED_ARealSourceInAClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "class C;\n"
      "  real src;\n"
      "  function int scan(); int v; return $sscanf(src, \"%d\", v); "
      "endfunction\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kStrKinds, 3, "21.3.4.3"));
}

TEST(SscanfSource, EveryAllowedSourceIsAccepted) {
  for (const char* decl :
       {"  string src;", "  logic [31:0] src;", "  int src;", "  byte src [4];",
        "  byte src [];", "  struct packed { byte a; byte b; } src;"}) {
    ElabFixture f;
    Elaborate(ScanFrom(decl), f);
    EXPECT_FALSE(f.has_errors) << decl;
  }
}

}  // namespace
