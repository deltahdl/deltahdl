#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(ClassItems, ClassPropertyMayBeANettypeDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  nettype logic [3:0] nt;\n"
      "  static nettype real rt;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1U);
  const auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 3U);
  for (int i = 0; i < 2; ++i) {
    EXPECT_EQ(members[i]->kind, ClassMemberKind::kTypedef);
    EXPECT_EQ(members[i]->typedef_item->kind, ModuleItemKind::kNettypeDecl);
  }
  EXPECT_EQ(members[0]->name, "nt");
  EXPECT_EQ(members[1]->name, "rt");
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(members[2]->name, "x");
}

TEST(ClassItems, NettypeDeclarationAdmitsNoMethodQualifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual nettype bit nb;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'virtual' is no qualifier of a nettype declaration", 2,
      "A.1.9"));
}

TEST(ClassItems, NettypeDeclarationIsNoInterfaceClassItem) {
  auto r = Parse(
      "interface class I;\n"
      "  nettype logic [3:0] nt;\n"
      "  typedef int t;\n"
      "endclass\n");
  const char* msg = "a nettype declaration is no item of an interface class";
  EXPECT_TRUE(ReportedError(r.diags, msg, 2, "A.1.9"));
  EXPECT_FALSE(ReportedError(r.diags, msg, 3, "A.1.9"));
}

void ExpectQualifiersReported(const std::string& item,
                              const std::string& message) {
  auto r = Parse("virtual class C;\n  " + item + "\nendclass\n");
  EXPECT_TRUE(ReportedError(r.diags, message, 2, "8.3")) << item;
}

void ExpectQualifiersAccepted(const std::string& item) {
  auto r = Parse("virtual class C;\n  " + item + "\nendclass\n");
  EXPECT_TRUE(r.diags.empty()) << item;
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members.size(), 1u) << item;
}

TEST(ClassItems, RandcTakesNoSecondRandomQualifier) {
  ExpectQualifiersReported("randc randc int x;", "duplicate 'randc' qualifier");
  ExpectQualifiersReported("randc rand int x;",
                           "cannot combine 'rand' and 'randc' qualifiers");
  ExpectQualifiersAccepted("randc int x;");
}

TEST(ClassItems, AMethodTakesOneVisibilityQualifierOnce) {
  const std::string kCombine = "cannot combine 'local' and 'protected'";
  for (const char* tail :
       {"function void f(); endfunction", "task t(); endtask",
        "function new(); endfunction"}) {
    const std::string kTail = tail;
    ExpectQualifiersReported("local protected " + kTail, kCombine);
    ExpectQualifiersReported("protected local " + kTail, kCombine);
    ExpectQualifiersReported("local local " + kTail,
                             "duplicate 'local' qualifier");
    ExpectQualifiersAccepted("local " + kTail);
  }
  for (const char* tail :
       {"function void f(); endfunction", "task t(); endtask"}) {
    const std::string kTail = tail;
    ExpectQualifiersReported("protected protected " + kTail,
                             "duplicate 'protected' qualifier");
    ExpectQualifiersReported("static static " + kTail,
                             "duplicate 'static' qualifier");
    ExpectQualifiersAccepted("protected " + kTail);
    ExpectQualifiersAccepted("static " + kTail);
  }
}

TEST(ClassItems, APrototypeTakesEachQualifierOnce) {
  ExpectQualifiersReported("extern local local function void f();",
                           "duplicate 'local' qualifier");
  ExpectQualifiersReported("extern protected local task t();",
                           "cannot combine 'local' and 'protected'");
  ExpectQualifiersReported(
      "pure virtual protected protected function void f();",
      "duplicate 'protected' qualifier");
  ExpectQualifiersReported("pure virtual local protected task t();",
                           "cannot combine 'local' and 'protected'");
  ExpectQualifiersAccepted("extern local function void f();");
  ExpectQualifiersAccepted("pure virtual protected function void f();");
}

TEST(ClassItems, DistinctMethodQualifiersMayComeInEitherOrder) {
  for (const char* item : {"protected virtual function void f(); endfunction",
                           "virtual protected function void f(); endfunction",
                           "local static function void f(); endfunction",
                           "static local function void f(); endfunction"}) {
    ExpectQualifiersAccepted(item);
  }
}

}  // namespace
