#include <gtest/gtest.h>

#include <cstdint>
#include <iostream>
#include <set>
#include <sstream>
#include <streambuf>
#include <string>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"

using namespace delta;

namespace {

// No clause of IEEE 1800-2023 says what a tool keeps about the diagnostics it
// has reported, so these cases cover DiagEngine on its own terms. What they
// establish is that a caller can tell one reported failure from another: the
// counts beside the records say how many errors there were and never which
// error, so an assertion that a run failed for the reason under test has to
// read the record itself.

// One real file for the diagnostics to be reported against, so a record
// carries a location it could have got wrong. Every case reports at a line and
// a column that differ from each other and from zero, so a record that dropped
// either of the two, or that kept the location a default-constructed record
// carries, reads differently from one that kept what it was given.
struct EngineFixture {
  SourceManager mgr;
  uint32_t file_id = mgr.AddFile("cell.sv",
                                 "module one_cell;\n"
                                 "endmodule\n");
  DiagEngine diag{mgr};

  SourceLoc Loc(uint32_t line, uint32_t column) const {
    return SourceLoc{file_id, line, column};
  }
};

TEST(Diagnostics, ErrorIsRecordedWithItsMessage) {
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().message,
            "two libraries claim this description");
  EXPECT_EQ(f.diag.Diagnostics().front().loc.line, 2u);
  EXPECT_EQ(f.diag.Diagnostics().front().loc.column, 4u);
}

TEST(Diagnostics, ErrorIsRecordedWithItsSeverity) {
  // A Diagnostic carries kError as its default severity, so a record that was
  // never given a severity at all still reads as an error. The warning
  // reported first is what makes the claim able to fail: code that stamped one
  // severity on every record it kept would have to stamp it on that one too.
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause::None());
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  EXPECT_EQ(f.diag.Diagnostics().back().severity, DiagSeverity::kError);
  EXPECT_NE(f.diag.Diagnostics().front().severity,
            f.diag.Diagnostics().back().severity);
}

TEST(Diagnostics, WarningIsRecordedWithItsSeverity) {
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().severity, DiagSeverity::kWarning);
}

// Whether sev is a value DiagSeverity declares. The switch gives every
// enumerator a case and declares no default label, so an enumerator added to
// DiagSeverity in src/common/diagnostic.h and not listed here fails the build
// under the -Wall -Wextra -Werror that CMakeLists.txt sets. That compile
// error is what catches a new enumerator, and
// Diagnostics.EverySeverityHasAProducer below is what then catches its having
// no entry point on DiagEngine that produces it. The trailing return is what
// a value cast in from outside the enumeration reaches.
bool IsDeclaredSeverity(DiagSeverity sev) {
  switch (sev) {
    case DiagSeverity::kWarning:
      return true;
    case DiagSeverity::kError:
      return true;
  }
  return false;
}

// Fails when DiagSeverity declares a severity that no entry point on
// DiagEngine can produce, which is the defect issue #3003 records. Asserting
// that kWarning and kError are producible would not catch that: an
// enumeration holding those two values plus an unproducible one satisfies
// such an assertion as much as an enumeration holding only the two does.
TEST(Diagnostics, EverySeverityHasAProducer) {
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause::None());
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  std::set<DiagSeverity> produced;
  for (const auto& d : f.diag.Diagnostics()) {
    produced.insert(d.severity);
  }

  std::set<DiagSeverity> declared;
  for (uint32_t raw = 0; raw <= 0xff; ++raw) {
    auto sev = static_cast<DiagSeverity>(static_cast<uint8_t>(raw));
    if (IsDeclaredSeverity(sev)) {
      declared.insert(sev);
    }
  }

  EXPECT_EQ(produced, declared);
}

TEST(Diagnostics, RecordsAreReturnedInTheOrderTheyWereReported) {
  // Two descriptions of one run fail for different reasons. A caller reading
  // the records back attributes each reason to the step that reported it, so
  // the order the records come in is the order they were reported in.
  EngineFixture f;
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v",
               Subclause::None());
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body",
               Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  EXPECT_EQ(f.diag.Diagnostics().front().message,
            "cannot read source description: absent.v");
  EXPECT_EQ(f.diag.Diagnostics().back().message,
            "unexpected token in module body");
}

TEST(Diagnostics, SuppressedDiagnosticIsNotRecorded) {
  // A speculative parse whose result is discarded reports errors that never
  // happened, and the engine suppresses them. The record it keeps has to
  // respect the suppression the counts already respect, or a caller reading
  // the records back learns of a failure the run did not have. The error
  // reported before the suppression is what shows the records were being kept
  // at all.
  EngineFixture f;
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v",
               Subclause::None());
  f.diag.PushSuppress();
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body",
               Subclause::None());
  f.diag.PopSuppress();

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().message,
            "cannot read source description: absent.v");
}

// A subclause of IEEE 1800-2023 is what the engine reports a rule from, and the
// cases below cover the record keeping it. The subclause a report names is
// separate from the sentence it reads out, so a caller can ask which rule was
// enforced without matching the wording of the sentence, and a reworded
// message leaves the answer alone. Every case names a subclause of three
// components, since the numbering is not arithmetic and code that stored it
// as a number would lose the third.

TEST(Diagnostics, SubclauseNamedInTheReportIsRecorded) {
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause("11.4.14"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().subclause, "11.4.14");
}

TEST(Diagnostics, SubclauseReportedWithAWarningIsRecorded) {
  // A warning enforces a rule as much as an error does, so the subclause
  // survives the path through the engine that an error does not take.
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause("16.12.17"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().subclause, "16.12.17");
}

TEST(Diagnostics, ReportStatingNoRuleOfTheStandardCarriesAnEmptySubclause) {
  // A report that enforces no rule of the standard says so with
  // Subclause::None(), and it has to read back as naming none rather than as
  // naming whatever the last report named. The subclause-bearing error reported
  // first is what makes that able to fail: an engine holding the subclause
  // across reports would hand it to the second one. Subclause::Unread() is
  // covered by
  // the same case, since the two are one value at run time and differ only in
  // the word the source uses.
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause("11.4.14"));
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v",
               Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  EXPECT_EQ(f.diag.Diagnostics().back().subclause, "");
}

TEST(Diagnostics, SubclauseIsPrintedWithTheMessage) {
  // A field nothing prints helps a test and no user, so the subclause reaches
  // the reader of the diagnostic as well as the reader of the record.
  // Diagnostics
  // are written to standard error, which the case redirects for the one report
  // it makes.
  EngineFixture f;
  std::ostringstream captured;
  std::streambuf* old_buf = std::cerr.rdbuf(captured.rdbuf());
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause("11.4.14"));
  std::cerr.rdbuf(old_buf);

  EXPECT_NE(captured.str().find("two libraries claim this description"),
            std::string::npos);
  EXPECT_NE(captured.str().find("(§11.4.14)"), std::string::npos);
}

// How many times *needle* occurs in *haystack*, so a case about a subclause
// being named twice asserts on a count rather than on the presence a single
// naming and a double naming both satisfy.
size_t CountOccurrences(const std::string& haystack,
                        const std::string& needle) {
  size_t count = 0;
  for (size_t at = haystack.find(needle); at != std::string::npos;
       at = haystack.find(needle, at + needle.size())) {
    ++count;
  }
  return count;
}

TEST(Diagnostics, SubclauseIsPrintedExactlyOnce) {
  // DiagEngine appends the subclause the caller passes in the field, so a
  // caller that also spells the subclause in its sentence prints it twice. The
  // rendered line is where the two meet, and nothing stores it, so the case
  // redirects standard error to read what a user reads.
  EngineFixture f;
  std::ostringstream captured;
  std::streambuf* old_buf = std::cerr.rdbuf(captured.rdbuf());
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause("11.4.14"));
  std::cerr.rdbuf(old_buf);

  EXPECT_EQ(CountOccurrences(captured.str(), "(§"), 1u);
}

TEST(Diagnostics, SuppressedDiagnosticWithASubclauseIsNotRecorded) {
  // A speculative parse reports rules broken by source the run goes on to
  // discard, and naming the subclause does not make one of those reports real.
  // The engine returns before it appends, so this holds today; the case is
  // what keeps a later edit from treating a subclause-bearing diagnostic as a
  // case worth recording through the suppression.
  EngineFixture f;
  f.diag.PushSuppress();
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause("11.4.14"));
  f.diag.PopSuppress();

  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(Diagnostics, WarningPromotedToAnErrorIsRecordedAsAnError) {
  // An invocation that asked for warnings to be errors gets a record saying
  // error, matching the count the same warning is added to. Without the
  // promotion this warning is recorded as a warning, which is what the case
  // above establishes.
  EngineFixture f;
  f.diag.SetWarningsAsErrors(true);
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().severity, DiagSeverity::kError);
}

TEST(Diagnostics, EveryReportedLocationIsValid) {
  // A record whose location never got filled in reads as <unknown location>
  // when it is written out, which tells a reader what went wrong and not where.
  // The engine takes whatever location it is given, so this is the case that
  // states the rule the reporting sites are held to: a report names a position
  // in the source. Both severities are reported here because either can reach
  // a reader with nothing but a sentence.
  EngineFixture f;
  f.diag.Error(f.Loc(1, 8), "reference through a null virtual interface",
               Subclause("25.9"));
  f.diag.Warning(f.Loc(2, 3), "bounded queue overflow in push_back",
                 Subclause("7.10.1"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_TRUE(d.loc.IsValid()) << d.message;
  }
}

}  // namespace
