// IEEE 1800-2023 Annex G.1 (Std package -- General).
//
// Section G.1 says what the built-in standard package contains: the semaphore
// class, the mailbox class, the randomize function, the process class and the
// weak reference class. src/elaborator/std_package.h writes that list down
// once, and the compilation-unit scope registers the std package's class names
// from it. These tests observe the list -- its five members, their names and
// kinds in the subclause's order, and the lookup of a member by name -- and
// that each member the list names is provided out of the std package at
// elaboration without a user definition, where a name the list does not hold
// is not.

#include <gtest/gtest.h>

#include <optional>
#include <string_view>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §G.1 lists five members, four classes and the randomize function, in the
// order semaphore, mailbox, randomize, process, weak reference.
TEST(StdPackageContents, TheAnnexListsFiveMembersInOrder) {
  const auto& contents = StdPackageContents();
  ASSERT_EQ(contents.size(), 5u);
  EXPECT_EQ(contents[0].member, StdPackageMember::kSemaphore);
  EXPECT_EQ(contents[0].name, "semaphore");
  EXPECT_EQ(contents[0].kind, StdPackageMemberKind::kClass);
  EXPECT_EQ(contents[1].member, StdPackageMember::kMailbox);
  EXPECT_EQ(contents[1].name, "mailbox");
  EXPECT_EQ(contents[1].kind, StdPackageMemberKind::kClass);
  EXPECT_EQ(contents[2].member, StdPackageMember::kRandomize);
  EXPECT_EQ(contents[2].name, "randomize");
  EXPECT_EQ(contents[2].kind, StdPackageMemberKind::kFunction);
  EXPECT_EQ(contents[3].member, StdPackageMember::kProcess);
  EXPECT_EQ(contents[3].name, "process");
  EXPECT_EQ(contents[3].kind, StdPackageMemberKind::kClass);
  EXPECT_EQ(contents[4].member, StdPackageMember::kWeakReference);
  EXPECT_EQ(contents[4].name, "weak_reference");
  EXPECT_EQ(contents[4].kind, StdPackageMemberKind::kClass);
}

// Each member answers to its name and kind, and a name the std package does
// not hold denotes no member.
TEST(StdPackageContents, AMemberIsFoundByItsName) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    EXPECT_EQ(StdPackageMemberName(entry.member), entry.name);
    EXPECT_EQ(KindOfStdPackageMember(entry.member), entry.kind);
    EXPECT_EQ(StdPackageMemberNamed(entry.name), entry.member);
  }
  EXPECT_EQ(StdPackageMemberNamed("queue"), std::nullopt);
  EXPECT_EQ(StdPackageMemberNamed("Semaphore"), std::nullopt);
  EXPECT_EQ(StdPackageMemberNamed(""), std::nullopt);
}

// The four classes the list names resolve without a user definition, and the
// randomize function is called through the std package, in one design.
TEST(StdPackageContents, EveryMemberIsProvidedWithoutAUserDefinition) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  semaphore sem;\n"
             "  mailbox mbx;\n"
             "  int v;\n"
             "  int q;\n"
             "  initial begin\n"
             "    process p = process::self();\n"
             "    weak_reference #(my_obj) wr;\n"
             "    q = std::randomize(v);\n"
             "  end\n"
             "endmodule\n"));
}

// A class name the list does not hold is not provided by the std package: a
// variable of that type is rejected under §6.18, no declaration preceding the
// reference, where the same declaration of a listed class is accepted.
TEST(StdPackageContents, ANameOutsideTheListIsNotProvided) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  semaphore sem;\n"
             "endmodule\n"));
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  barrier sem;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "declaration of type 'barrier' does not precede this reference to it", 2,
      "6.18"));
}

}  // namespace
