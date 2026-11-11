#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

TEST(ClassDeclaration, MalformedClassItemNames8_3) {
  auto r = Parse(
      "class C;\n"
      "  local protected int x;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot combine 'local' and 'protected' qualifiers", 2, "8.3"));
}

TEST(ClassDeclaration, ClassItemWithOneAccessQualifierIsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  local int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassDeclaration, ALifetimeAfterClassIsReported) {
  auto r = Parse(
      "class automatic A; endclass\n"
      "class static B; endclass\n"
      "module m; A a; B b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "a class declaration takes no lifetime; "
                            "'automatic' stands where its name belongs",
                            1, "8.3"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "a class declaration takes no lifetime; "
                            "'static' stands where its name belongs",
                            2, "8.3"));
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "A");
  EXPECT_EQ(r.cu->classes[1]->name, "B");
}

TEST(ClassDeclaration, ARepeatedOrClashingQualifierIsReported) {
  auto r = Parse(
      "class C;\n"
      "  randc randc bit [1:0] a;\n"
      "  randc rand bit [1:0] b;\n"
      "  static static function void f(); endfunction\n"
      "  local local task t(); endtask\n"
      "  protected protected function void g(); endfunction\n"
      "  protected local function void h(); endfunction\n"
      "  virtual virtual task u(); endtask\n"
      "  static local static int y;\n"
      "  extern static static function void p();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "duplicate 'randc' qualifier", 2, "8.3"));
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot combine 'rand' and 'randc' qualifiers", 3, "8.3"));
  EXPECT_TRUE(ReportedError(r.diags, "duplicate 'static' qualifier", 4, "8.3"));
  EXPECT_TRUE(ReportedError(r.diags, "duplicate 'local' qualifier", 5, "8.3"));
  EXPECT_TRUE(
      ReportedError(r.diags, "duplicate 'protected' qualifier", 6, "8.3"));
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot combine 'local' and 'protected' qualifiers", 7, "8.3"));
  EXPECT_TRUE(
      ReportedError(r.diags, "duplicate 'virtual' qualifier", 8, "8.3"));
  EXPECT_TRUE(ReportedError(r.diags, "duplicate 'static' qualifier", 9, "8.3"));
  EXPECT_TRUE(
      ReportedError(r.diags, "duplicate 'static' qualifier", 10, "8.3"));
}

TEST(ClassDeclaration, EachQualifierWrittenOnceIsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  randc static local bit [1:0] a;\n"
      "  static rand protected int b;\n"
      "  local static function void f(); endfunction\n"
      "  protected virtual task t(); endtask\n"
      "  extern static protected function void p();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassDeclaration, ASecondDefaultOutsideTheConstructorBodyIsReported) {
  auto r = Parse(
      "class B; function new(int a); endfunction endclass\n"
      "class C extends B;\n"
      "  extern function new(default, default);\n"
      "endclass\n"
      "class D extends B;\n"
      "  extern function new(default);\n"
      "endclass\n"
      "function D::new(int y, default, int z, default);\n"
      "  super.new(default);\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  const char* const kMsg =
      "'default' already appears earlier in this class constructor argument "
      "list";
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 3, "8.17"));
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 8, "8.17"));
  EXPECT_FALSE(ReportedError(r.diags, kMsg, 6, "8.17"));
}

TEST(ClassDeclaration, OneDefaultOutsideTheConstructorBodyIsAccepted) {
  auto r = Parse(
      "class B; function new(int a); endfunction endclass\n"
      "class C extends B;\n"
      "  extern function new(int y, default);\n"
      "endclass\n"
      "function C::new(int y, default);\n"
      "  super.new(default);\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassDeclaration,
     DISABLED_AConstructorWrittenWithAnOverrideSpecifierIsReported) {
  auto r = Parse(
      "class C; function :initial new(); endfunction endclass\n"
      "class D; function :extends new(); endfunction endclass\n"
      "class E; function :final new(); endfunction endclass\n"
      "class F; function :initial :final new(); endfunction endclass\n"
      "class G; extern function :final new(); endclass\n"
      "package p;\n"
      "  class H; function :extends new(int a); endfunction endclass\n"
      "endpackage\n"
      "module m;\n"
      "  class K; function :final new(); endfunction endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  for (uint32_t line : {1u, 2u, 3u, 4u, 5u, 7u, 10u}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "a class constructor takes no dynamic_override_specifiers",
        line, "8.3"))
        << line;
  }
}

TEST(ClassDeclaration,
     DISABLED_AConstructorWrittenWithAnAutomaticLifetimeIsReported) {
  auto r = Parse(
      "class C; function automatic new(); endfunction endclass\n"
      "package p;\n"
      "  class D; function automatic new(int a); endfunction endclass\n"
      "endpackage\n"
      "module m;\n"
      "  class E; function automatic new(); endfunction endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  for (uint32_t line : {1u, 3u, 6u}) {
    EXPECT_TRUE(ReportedError(r.diags, "a class constructor takes no lifetime",
                              line, "8.3"))
        << line;
  }
}

TEST(ClassDeclaration,
     AConstructorWithAStaticLifetimeOrALifetimedPrototypeIsReported) {
  auto r = Parse(
      "class C; function static new(); endfunction endclass\n"
      "class D; extern function automatic new(); endclass\n"
      "function D::new(); endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "class method shall not have static lifetime", 1, "8.6"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a class method prototype takes no lifetime", 2, "A.1.9"));
}

TEST(ClassDeclaration, AConstructorWithoutSpecifierOrLifetimeIsAccepted) {
  auto r = Parse(
      "class C; function new(); endfunction endclass\n"
      "class D; extern function new(int a); endclass\n"
      "function D::new(int a); endfunction\n"
      "class E; local function new(); endfunction : new endclass\n"
      "package p; class F; function new(); endfunction endclass endpackage\n"
      "module m; class G; function new(); endfunction endclass endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
