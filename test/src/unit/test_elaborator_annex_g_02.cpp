#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StdPackageOverview, EachMemberHasTheDefiningSubclauseItsPrototypeNames) {
  EXPECT_EQ(DefiningSubclauseOfStdPackageMember(StdPackageMember::kSemaphore),
            "15.3");
  EXPECT_EQ(DefiningSubclauseOfStdPackageMember(StdPackageMember::kMailbox),
            "15.4");
  EXPECT_EQ(DefiningSubclauseOfStdPackageMember(StdPackageMember::kRandomize),
            "18.12");
  EXPECT_EQ(DefiningSubclauseOfStdPackageMember(StdPackageMember::kProcess),
            "9.7");
  EXPECT_EQ(
      DefiningSubclauseOfStdPackageMember(StdPackageMember::kWeakReference),
      "8.30");
  for (const StdPackageEntry& entry : StdPackageContents()) {
    EXPECT_EQ(DefiningSubclauseOfStdPackageMember(entry.member),
              entry.defining_subclause);
    EXPECT_EQ(PrototypeSubclauseOfStdPackageMember(entry.member),
              entry.prototype_subclause);
  }
  EXPECT_EQ(PrototypeSubclauseOfStdPackageMember(StdPackageMember::kSemaphore),
            "G.3");
  EXPECT_EQ(
      PrototypeSubclauseOfStdPackageMember(StdPackageMember::kWeakReference),
      "G.7");
}

TEST(StdPackageOverview, ASubclauseLiesInTheDefiningOneOrBeneathIt) {
  EXPECT_TRUE(
      StdPackageDefinesSemanticsIn(StdPackageMember::kWeakReference, "8.30"));
  EXPECT_TRUE(
      StdPackageDefinesSemanticsIn(StdPackageMember::kWeakReference, "8.30.1"));
  EXPECT_FALSE(
      StdPackageDefinesSemanticsIn(StdPackageMember::kWeakReference, "8.3"));
  EXPECT_FALSE(
      StdPackageDefinesSemanticsIn(StdPackageMember::kWeakReference, "8.301"));
  EXPECT_TRUE(
      StdPackageDefinesSemanticsIn(StdPackageMember::kMailbox, "15.4.9"));
  EXPECT_FALSE(
      StdPackageDefinesSemanticsIn(StdPackageMember::kSemaphore, "15.4.9"));
  EXPECT_FALSE(StdPackageDefinesSemanticsIn(StdPackageMember::kProcess, ""));
}

TEST(StdPackageOverview, TheSystemTypesAreThePackagesClasses) {
  EXPECT_TRUE(IsStdPackageSystemType("semaphore"));
  EXPECT_TRUE(IsStdPackageSystemType("mailbox"));
  EXPECT_TRUE(IsStdPackageSystemType("process"));
  EXPECT_TRUE(IsStdPackageSystemType("weak_reference"));
  EXPECT_FALSE(IsStdPackageSystemType("randomize"));
  EXPECT_FALSE(IsStdPackageSystemType("queue"));
}

TEST(StdPackageOverview, ARejectedUseOfAStdTypeCitesTheDefiningSubclause) {
  ElabFixture process_fixture;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    process p;\n"
      "    p = new;\n"
      "  end\n"
      "endmodule\n",
      process_fixture);
  EXPECT_TRUE(ReportedError(process_fixture.diag.Diagnostics(),
                            "cannot construct a process object with 'new'", 4,
                            "9.7"));
  EXPECT_TRUE(StdPackageDefinesSemanticsIn(StdPackageMember::kProcess, "9.7"));

  ElabFixture weak_fixture;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(int) wr;\n"
      "  end\n"
      "endmodule\n",
      weak_fixture);
  EXPECT_TRUE(ReportedError(
      weak_fixture.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 3, "8.30.1"));
  EXPECT_TRUE(
      StdPackageDefinesSemanticsIn(StdPackageMember::kWeakReference, "8.30.1"));

  ElabFixture mailbox_fixture;
  ElabOk(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    mb.put(s);\n"
      "  end\n"
      "endmodule\n",
      mailbox_fixture);
  EXPECT_TRUE(ReportedError(
      mailbox_fixture.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 5, "15.4.9"));
  EXPECT_TRUE(
      StdPackageDefinesSemanticsIn(StdPackageMember::kMailbox, "15.4.9"));
}

}  // namespace
