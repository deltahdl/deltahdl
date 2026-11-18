#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(ScopeResolutionPrefixElaboration, PackagePrefixResolvesDownward) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module t;\n"
             "  pkg::byte_t x;\n"
             "endmodule\n"));
}

TEST(ScopeResolutionPrefixElaboration, ClassPrefixResolvesDownward) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  typedef int my_type;\n"
             "endclass\n"
             "module t;\n"
             "  C::my_type x;\n"
             "endmodule\n"));
}

TEST(ScopedNameMembers, DISABLED_APackagePrefixDoesNotReachTheModule) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n  int y;\nendpackage\n"
      "module t;\n  int z;\n  initial z = p::z;\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'p::z', which package 'p' neither "
                            "declares nor exports",
                            6, "23.7.1"));
}

TEST(ScopedNameMembers, DISABLED_AClassPrefixDoesNotReachTheModule) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n  int z;\n  class C;\n    static int y;\n  endclass\n"
      "  initial z = C::z;\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'C' has no member named 'z'", 6, "23.7.1"));
}

TEST(ScopedNameMembers, AMemberOfTheNamedScopeIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n  int z;\nendpackage\n"
      "module t;\n  int z;\n  class C;\n    static int z;\n  endclass\n"
      "  initial z = p::z + C::z;\nendmodule\n",
      f, "t");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
