#include "fixture_elaborator.h"

namespace {

// --- Requirement 1: :: prefix resolves downward ---

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

TEST(ScopeResolutionPrefixElaboration, ChainedPrefixResolvesDownward) {
  EXPECT_TRUE(
      ElabOk("class Outer;\n"
             "  class Inner;\n"
             "    typedef int deep_type;\n"
             "  endclass\n"
             "endclass\n"
             "module t;\n"
             "  Outer::Inner::deep_type x;\n"
             "endmodule\n"));
}

// --- Requirement 3: class vs. package disambiguation ---

TEST(ScopeResolutionPrefixElaboration, ClassAndPackagePrefixesCoexist) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [15:0] word_t;\n"
             "endpackage\n"
             "class Cfg;\n"
             "  typedef int cfg_type;\n"
             "endclass\n"
             "module t;\n"
             "  pkg::word_t a;\n"
             "  Cfg::cfg_type b;\n"
             "endmodule\n"));
}

TEST(ScopeResolutionPrefixElaboration, VisibleClassPrefixDenotesClassScope) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  typedef int inner_t;\n"
             "endclass\n"
             "module t;\n"
             "  C::inner_t x;\n"
             "endmodule\n"));
}

TEST(ScopeResolutionPrefixElaboration, UnresolvablePrefixDenotesPackageScope) {
  EXPECT_TRUE(
      ElabOk("package ext;\n"
             "  typedef logic [31:0] wide_t;\n"
             "endpackage\n"
             "module t;\n"
             "  ext::wide_t x;\n"
             "endmodule\n"));
}

}  // namespace
