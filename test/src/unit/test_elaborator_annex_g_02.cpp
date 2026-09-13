// IEEE 1800-2023 Annex G.2 (Std package -- Overview).
//
// Section G.2 says two things of the std built-in package: that it contains
// system types, the ones §26.7 has it provide, and that the semantics of the
// types it provides are defined not in the annex but in the subclauses its
// prototypes indicate. src/elaborator/std_package.h carries both: the
// defining subclause of each member and the reading of the package's classes
// as its system types. These tests observe the defining subclause each
// prototype of §G.3 through §G.7 names, which names denote a system type, and
// that when the elaborator rejects a use of a std type it does so under the
// subclause §G.2 points to for that type, or one beneath it.

#include <string_view>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §G.2 with §G.3 through §G.7: semaphore is described in §15.3, mailbox in
// §15.4, randomize in §18.12, process in §9.7 and weak_reference in §8.30.
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

// A subclause lies where a member's semantics are defined iff it is the
// indicated subclause or one beneath it: §8.30.1 lies in §8.30, §8.3 and
// §8.301 do not, and §15.4.9 lies in mailbox's §15.4 and not in semaphore's
// §15.3.
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

// §G.2: the system types the package contains are its classes; randomize is
// a function, not a type, and a name outside the package denotes no type.
TEST(StdPackageOverview, TheSystemTypesAreThePackagesClasses) {
  EXPECT_TRUE(IsStdPackageSystemType("semaphore"));
  EXPECT_TRUE(IsStdPackageSystemType("mailbox"));
  EXPECT_TRUE(IsStdPackageSystemType("process"));
  EXPECT_TRUE(IsStdPackageSystemType("weak_reference"));
  EXPECT_FALSE(IsStdPackageSystemType("randomize"));
  EXPECT_FALSE(IsStdPackageSystemType("queue"));
}

// §G.2: the semantics are the indicated subclause's. A process constructed
// with new is rejected under §9.7, a weak_reference over a non-class type
// under §8.30.1 and a mailbox put of a mistyped argument under §15.4.9, each
// where §G.2 says the type's semantics are defined.
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
      "weak_reference type parameter shall be a class type", 3, "8.30.1"));
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
