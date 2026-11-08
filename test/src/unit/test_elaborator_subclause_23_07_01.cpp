#include <gtest/gtest.h>

#include "fixture_elaborator.h"

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

}  // namespace
