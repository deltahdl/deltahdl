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
  // Parser::ParseDynamicOverrideSpecifiers records whichever specifier comes
  // first, so a check written only for `extends` after `initial` passes the
  // case above and fails this one.
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

// The line §8.20 Example 3 prints (printed page 198), under the comment the
// standard gives it: "OK: f2 shall not be overridden in subclasses of A". The
// order is the one the normative grammar does not admit --
// `dynamic_override_specifiers ::= [ initial_or_extends_specifier ]
// [ final_specifier ]` is printed in Syntax 8-1 and again in A.2.7, under an
// annex titled "(normative) Formal syntax" -- so the source is reported, and
// what it is reported for is the order.
//
// The case fails on a run that says anything else about this line. Before the
// specifiers were read in a loop, `extends` was left standing where the name
// belongs and Parser::ParseFuncName reported the method as having no name under
// §13.4, which answers a question nobody asked.
TEST(VirtualMethodParsing, FinalBeforeExtendsIsRejected) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :final :extends void f2(); endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "':final' is written after ':initial' or ':extends'", 2,
      "8.20"));
}

// §8.20 permits `final` with `initial` in the sentence that permits it with
// `extends`, so the grammar orders both pairs and both are reported when
// reversed. Without this case a check keyed on `extends` alone passes
// VirtualMethodParsing.FinalBeforeExtendsIsRejected and lets `:final :initial`
// through.
TEST(VirtualMethodParsing, FinalBeforeInitialIsRejected) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :final :initial my_task(); endtask\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "':final' is written after ':initial' or ':extends'", 2,
      "8.20"));
}

// The order is all that is wrong, so both specifiers are recorded and the
// method still has its name. That is what separates this report from the §13.4
// one it replaces: a reader is told what to move rather than that `f2` is
// missing, and a second defect in the same declaration is not hidden behind the
// first. Exactly one error is what states the §13.4 cascade is gone.
TEST(VirtualMethodParsing, FinalBeforeExtendsStillReadsTheMethodAndItsFlags) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :final :extends void f2(); endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->name, "f2");
  EXPECT_TRUE(m->is_method_extends);
  EXPECT_TRUE(m->is_method_final);
  uint32_t errors = 0;
  for (const auto& d : r.diags) {
    if (d.severity == DiagSeverity::kError) errors++;
  }
  EXPECT_EQ(errors, 1U);
}

// Syntax 8-1 gives one final_specifier, so a second is what a parser reading
// specifiers in a loop must refuse. This was accepted before the loop, the two
// hand-written positions each admitting `final` once.
TEST(VirtualMethodParsing, FinalTwiceIsRejected) {
  auto r = Parse(
      "class C;\n"
      "  function :final :final void f(); endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a method takes at most one ':final' specifier", 2, "8.20"));
}

// Syntax 8-1 gives one initial_or_extends_specifier as well, and a repeat that
// does not change the specifier is not the pair §8.20 calls mutually exclusive,
// so it answers to the counting rule and not to that message. Left unreported
// it would stand where the method name belongs and draw §13.4, which is the
// report this issue is about.
TEST(VirtualMethodParsing, InitialTwiceIsRejected) {
  auto r = Parse(
      "class C;\n"
      "  function :initial :initial void f(); endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a method takes at most one ':initial' or ':extends' specifier",
      2, "8.20"));
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
