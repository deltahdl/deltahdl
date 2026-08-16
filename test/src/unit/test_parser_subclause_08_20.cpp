#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(VirtualMethodParsing, DerivedOverrideWithoutVirtual) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  virtual function void display(); endfunction\n"
              "endclass\n"
              "class Derived extends Base;\n"
              "  function void display(); endfunction\n"
              "endclass\n"));
}

TEST(VirtualMethodParsing, MethodInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :initial void foo(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, MethodExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :extends void bar(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

// §8.20 (printed page 197): "initial and extends are mutually exclusive;
// specifying both in a method declaration shall result in an error." The three
// cases above accept each specifier alone, which is what keeps this one from
// being satisfied by a parser that refused every specifier.
TEST(VirtualMethodParsing, InitialAndExtendsTogetherIsRejected) {
  auto r = Parse(
      "class C;\n"
      "  function :initial :extends void foo(); endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "':initial' and ':extends' are mutually exclusive", 2, "8.20"));
}

TEST(VirtualMethodParsing, ExtendsThenInitialIsRejected) {
  // Parser::ParseOneOverrideSpecifier takes whichever specifier comes first, so
  // a check written only for `extends` after `initial` passes the case above
  // and fails this one.
  auto r = Parse(
      "class C;\n"
      "  function :extends :initial void foo(); endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "':initial' and ':extends' are mutually exclusive", 2, "8.20"));
}

TEST(VirtualMethodParsing, InitialAndExtendsTogetherReportsExactlyOneError) {
  // The second specifier is consumed, so `foo` is still read as the method
  // name. It used to stand where the name belongs, and Parser::ParseFuncName
  // reported it a second time under §13.4.
  auto r = Parse(
      "class C;\n"
      "  function :initial :extends void foo(); endfunction\n"
      "endclass\n");
  uint32_t errors = 0;
  for (const auto& d : r.diags) {
    if (d.severity == DiagSeverity::kError) errors++;
  }
  EXPECT_EQ(errors, 1U);
}

TEST(VirtualMethodParsing, InitialAndExtendsTogetherStoresOnlyTheFirst) {
  // The rejected specifier is not recorded, which is what makes the pair
  // unreachable in Elaborator::ValidateOneMethodOverride rather than merely
  // unreported here.
  auto r = Parse(
      "class C;\n"
      "  function :initial :extends void foo(); endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->name, "foo");
  EXPECT_TRUE(m->is_method_initial);
  EXPECT_FALSE(m->is_method_extends);
}

TEST(VirtualMethodParsing, MethodFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :final void baz(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, MethodInitialFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  function :initial :final void qux(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, TaskExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  task :extends my_task(); endtask\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualTaskExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualTaskFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualTaskInitialFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualTaskExtendsFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, InitialSpecifierStored) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_initial);
  EXPECT_FALSE(m->is_method_extends);
  EXPECT_FALSE(m->is_method_final);
}

TEST(VirtualMethodParsing, ExtendsSpecifierStored) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_FALSE(m->is_method_initial);
  EXPECT_TRUE(m->is_method_extends);
}

TEST(VirtualMethodParsing, FinalSpecifierStored) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :final int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_final);
}

TEST(VirtualMethodParsing, InitialFinalCombined) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_initial);
  EXPECT_TRUE(m->is_method_final);
}

TEST(VirtualMethodParsing, ExtendsFinalCombined) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_extends);
  EXPECT_TRUE(m->is_method_final);
}

TEST(VirtualMethodParsing, TaskInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_initial);
}

}  // namespace
