#include <gtest/gtest.h>

#include <optional>
#include <string_view>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
             "    static process p = process::self();\n"
             "    weak_reference #(my_obj) wr;\n"
             "    q = std::randomize(v);\n"
             "  end\n"
             "endmodule\n"));
}

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
