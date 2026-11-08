#include <gtest/gtest.h>

#include <cstddef>
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

bool IsDeclaredSeverity(DiagSeverity sev) {
  switch (sev) {
    case DiagSeverity::kWarning:
    case DiagSeverity::kError:
      return true;
  }
  return false;
}

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

TEST(Diagnostics, SuppressedWarningIsNotCountedAsASuppressedError) {
  EngineFixture f;
  f.diag.PushSuppress();
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause::None());
  EXPECT_EQ(f.diag.SuppressedErrorCount(), 0u);
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body",
               Subclause::None());
  f.diag.PopSuppress();

  EXPECT_EQ(f.diag.SuppressedErrorCount(), 1u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(Diagnostics, ReportWithoutAColumnQuotesItsLineWithoutACaret) {
  EngineFixture f;
  std::ostringstream captured;
  std::streambuf* old_buf = std::cerr.rdbuf(captured.rdbuf());
  f.diag.Error(f.Loc(2, 0), "two libraries claim this description",
               Subclause::None());
  std::cerr.rdbuf(old_buf);

  EXPECT_NE(captured.str().find("  endmodule\n"), std::string::npos);
  EXPECT_EQ(captured.str().find('^'), std::string::npos);
}

TEST(Diagnostics, SubclauseNamedInTheReportIsRecorded) {
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause("11.4.14"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().subclause, "11.4.14");
}

TEST(Diagnostics, SubclauseReportedWithAWarningIsRecorded) {
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause("16.12.17"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().subclause, "16.12.17");
}

TEST(Diagnostics, ReportStatingNoRuleOfTheStandardCarriesAnEmptySubclause) {
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause("11.4.14"));
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v",
               Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  EXPECT_EQ(f.diag.Diagnostics().back().subclause, "");
}

TEST(Diagnostics, SubclauseIsPrintedWithTheMessage) {
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
  EngineFixture f;
  std::ostringstream captured;
  std::streambuf* old_buf = std::cerr.rdbuf(captured.rdbuf());
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause("11.4.14"));
  std::cerr.rdbuf(old_buf);

  EXPECT_EQ(CountOccurrences(captured.str(), "(§"), 1u);
}

TEST(Diagnostics, SuppressedDiagnosticWithASubclauseIsNotRecorded) {
  EngineFixture f;
  f.diag.PushSuppress();
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause("11.4.14"));
  f.diag.PopSuppress();

  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(Diagnostics, WarningPromotedToAnErrorIsRecordedAsAnError) {
  EngineFixture f;
  f.diag.SetWarningsAsErrors(true);
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().severity, DiagSeverity::kError);
}

TEST(Diagnostics, EveryReportedLocationIsValid) {
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

TEST(Diagnostics, EveryQueryOfTheRecordCountsAsARead) {
  EngineFixture f;
  static_cast<void>(f.diag.HasErrors());
  static_cast<void>(f.diag.ErrorCount());
  static_cast<void>(f.diag.WarningCount());
  static_cast<void>(f.diag.Diagnostics());
  static_cast<void>(f.diag.SuppressedErrorCount());
  static_cast<void>(f.diag.LastSuppressedErrorLoc());

  EXPECT_EQ(f.diag.ReadCount(), 6u);
}

TEST(Diagnostics, AnErrorIsUnreadUntilTheRecordIsQueried) {
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause::None());
  EXPECT_TRUE(f.diag.HasUnreadError());

  static_cast<void>(f.diag.Diagnostics());

  EXPECT_FALSE(f.diag.HasUnreadError());
}

TEST(Diagnostics, AQueryBeforeAnErrorDoesNotReadIt) {
  EngineFixture f;
  static_cast<void>(f.diag.Diagnostics());
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body",
               Subclause::None());

  EXPECT_TRUE(f.diag.HasUnreadError());
}

TEST(Diagnostics, AnErrorAfterTheLastQueryIsUnreadAgain) {
  EngineFixture f;
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v",
               Subclause::None());
  static_cast<void>(f.diag.Diagnostics());
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body",
               Subclause::None());

  EXPECT_TRUE(f.diag.HasUnreadError());
}

TEST(Diagnostics, AWarningLeavesNoErrorUnread) {
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause::None());

  EXPECT_FALSE(f.diag.HasUnreadError());
}

TEST(Diagnostics, AWarningPromotedToAnErrorIsUnread) {
  EngineFixture f;
  f.diag.SetWarningsAsErrors(true);
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Subclause::None());

  EXPECT_TRUE(f.diag.HasUnreadError());
}

TEST(Diagnostics, ASuppressedErrorLeavesNoErrorUnread) {
  EngineFixture f;
  f.diag.PushSuppress();
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body",
               Subclause::None());
  f.diag.PopSuppress();

  EXPECT_FALSE(f.diag.HasUnreadError());
}

TEST(Diagnostics, AskingWhetherTheRecordWasReadIsNotItselfARead) {
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Subclause::None());
  uint32_t reads_before = f.diag.ReadCount();

  EXPECT_TRUE(f.diag.HasUnreadError());
  EXPECT_TRUE(f.diag.HasUnreadError());
  EXPECT_EQ(f.diag.ReadCount(), reads_before);
}

}  // namespace
