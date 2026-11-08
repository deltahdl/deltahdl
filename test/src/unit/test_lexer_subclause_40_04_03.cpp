#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

struct ConcatPragmaInfo {
  std::vector<std::string> signals;
  std::string fsm_name;
  std::string enum_name;
};

std::vector<ConcatPragmaInfo> CollectConcatPragmas(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  std::vector<ConcatPragmaInfo> out;
  for (const auto& p : lexer.FsmConcatPragmas()) {
    ConcatPragmaInfo info;
    for (const auto& s : p.signal_names) {
      info.signals.push_back(std::string(s));
    }
    info.fsm_name = std::string(p.fsm_name);
    info.enum_name = std::string(p.enum_name);
    out.push_back(std::move(info));
  }
  return out;
}

TEST(FsmConcatPragmaLexing, ComposedOfAllSignalsWithIrregularSpacing) {
  auto pragmas =
      CollectConcatPragmas("/* tool state_vector { a , b,c } my_fsm enum e */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signals, (std::vector<std::string>{"a", "b", "c"}));
}

TEST(FsmConcatPragmaLexing, SingleSignalConcatenationRecordsThatSignal) {
  auto pragmas = CollectConcatPragmas(
      "/* tool state_vector {only} my_fsm enum state_e "
      "*/");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signals, (std::vector<std::string>{"only"}));
  EXPECT_EQ(pragmas[0].fsm_name, "my_fsm");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

TEST(FsmConcatPragmaLexing, BitSelectOrPartSelectMemberRejected) {
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi[0], lo} my_fsm enum e */")
          .empty());
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi[3:0], lo} my_fsm enum e "
                           "*/")
          .empty());
}

TEST(FsmConcatPragmaLexing, RequiresFsmNameAndEnumBinding) {
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi, lo} enum state_e */")
          .empty());
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi, lo} my_fsm uses state_e "
                           "*/")
          .empty());
}

TEST(FsmConcatPragmaLexing, EmptyConcatenationIsNotRecognized) {
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {} my_fsm enum state_e */")
          .empty());
}

TEST(FsmConcatPragmaLexing, UnclosedBraceIsNotRecognized) {
  EXPECT_TRUE(
      CollectConcatPragmas("/* tool state_vector {hi, lo my_fsm enum state_e "
                           "*/")
          .empty());
}

TEST(FsmConcatPragmaLexing, ConcatIsSeparateFromOtherFsmPragmas) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  const std::string kSrc = "/* tool state_vector {hi, lo} my_fsm enum e */";
  auto fid = mgr.AddFile("<test>", kSrc);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_EQ(lexer.FsmConcatPragmas().size(), 1u);
  EXPECT_TRUE(lexer.FsmStatePragmas().empty());
  EXPECT_TRUE(lexer.FsmPartSelectPragmas().empty());
}

TEST(FsmConcatPragmaLexing, RecognizedWithinModuleBody) {
  const std::string kSrc =
      "module fsm;\n"
      "  logic hi;\n"
      "  logic lo;\n"
      "  /* tool state_vector {hi, lo} my_fsm enum state_e */\n"
      "endmodule\n";
  auto pragmas = CollectConcatPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signals, (std::vector<std::string>{"hi", "lo"}));
  EXPECT_EQ(pragmas[0].fsm_name, "my_fsm");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

TEST(FsmConcatPragmaLexing, SelectMemberIsReportedAgainstTheProhibition) {
  const std::string kSrc =
      "module fsm;\n"
      "  logic [3:0] hi;\n"
      "  logic lo;\n"
      "  /* tool state_vector {hi[3:0], lo} my_fsm enum state_e */\n"
      "endmodule\n";

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", kSrc);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();

  EXPECT_TRUE(lexer.FsmConcatPragmas().empty());
  EXPECT_TRUE(ReportedWarning(
      diag.Diagnostics(),
      "bit-select or part-select cannot be used in an FSM state_vector "
      "concatenation",
      LineHolding(kSrc, "/* tool state_vector"), "40.4.3"));
}

TEST(FsmConcatPragmaLexing, NothingIsReportedWhereNoSelectWasWritten) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "/* tool state_vector {hi lo} my_fsm enum e */\n"
                         "/* an ordinary comment */\n");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();

  EXPECT_TRUE(lexer.FsmConcatPragmas().empty());
  EXPECT_TRUE(diag.Diagnostics().empty());
}

TEST(FsmConcatPragmaLexing, MissingOrMalformedNamesAreNotRecognized) {
  for (const char* tail : {"my_fsm enum", "my_fsm with state_e",
                           "9fsm enum state_e", "my_fsm enum 9e"}) {
    EXPECT_TRUE(CollectConcatPragmas(
                    std::string("/* tool state_vector {a, b} ") + tail + " */")
                    .empty())
        << tail;
  }
}

}  // namespace
