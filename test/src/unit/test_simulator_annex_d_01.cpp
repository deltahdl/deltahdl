#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

// Annex D.1: general.
//
// D.1 has the system tasks and system functions Annex D describes "for
// informative purposes only", "not part of this standard", and "may not be
// available in all implementations", and lists the twenty of them under the
// subclause that describes each. A call of one this implementation is without
// is what D.1 allows, so the call is reported under D.1 as the annex's optional
// task, naming the subclause that describes it, rather than as a name that is
// no system task or system function at all, which is §20.1's report for a name
// outside the standard's catalogue and which every such call got.

using namespace delta;

namespace {

// Elaborate, lower and run `src`, which is how a $name in a source reaches the
// dispatch chain that classifies it. Returns false when the source did not
// elaborate, which a case reads as having covered nothing.
bool RunAnnexDSource(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return false;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return true;
}

// A source calling `call` as a statement; the call stands on line 2.
std::string AsTask(const std::string& call) {
  return "module t;\n"
         "  initial " +
         call +
         ";\n"
         "endmodule\n";
}

// The report D.1 owes a call of an optional task or function that is not
// available here.
std::string NotAvailable(const std::string& name, const std::string& sub) {
  return name + " is the optional system task or system function " + sub +
         " describes, which Annex D.1 has \"may not be available in all "
         "implementations\"; this implementation is one without it";
}

// D.5's $key, an interactive task with no place in a batch simulator.
TEST(OptionalSystemTasksGeneral, AnUnavailableKeyTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$key")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAvailable("$key", "D.5"),
                            2, "D.1"));
}

// D.4's $input, with the argument its syntax takes.
TEST(OptionalSystemTasksGeneral, AnUnavailableInputTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$input(\"cmds.txt\")")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAvailable("$input", "D.4"),
                            2, "D.1"));
}

// D.9's three, of which $save is the one with an argument; the name stands
// last in D.1's list, so the whole of it is searched.
TEST(OptionalSystemTasksGeneral, AnUnavailableSaveTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$save(\"state.dat\")")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAvailable("$save", "D.9"),
                            2, "D.1"));
}

// D.5's $nokey, the task beside $key, which stands in D.1's list under the
// same subclause.
TEST(OptionalSystemTasksGeneral, AnUnavailableNokeyTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$nokey")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAvailable("$nokey", "D.5"),
                            2, "D.1"));
}

// The control: an optional task this implementation does provide, D.6's
// $list, is carried out and reported as nothing.
TEST(OptionalSystemTasksGeneral, AnAvailableOptionalTaskIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$list")));
  EXPECT_FALSE(f.diag.HasErrors());
}

// The other control: a name D.1 does not list is still §20.1's report, so the
// D.1 one is owed to the annex's names alone.
TEST(OptionalSystemTasksGeneral, ANameOutsideAnnexDKeepsTheCatalogueReport) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$keyboard")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$keyboard is not a system task or system "
                            "function this tool implements",
                            2, "20.1"));
}

}  // namespace
