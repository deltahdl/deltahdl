#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_fsm_pragma_lexing.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

struct FsmPartSelectInfo {
  std::string signal;
  int msb = 0;
  int lsb = 0;
  std::string fsm_name;
  std::string enum_name;
};

std::vector<FsmPartSelectInfo> CollectPartSelectPragmas(
    const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  std::vector<FsmPartSelectInfo> out;
  for (const auto& p : lexer.FsmPartSelectPragmas()) {
    out.push_back({std::string(p.signal_name), p.msb, p.lsb,
                   std::string(p.fsm_name), std::string(p.enum_name)});
  }
  return out;
}

struct FsmConcatInfo {
  std::vector<std::string> signals;
  std::string fsm_name;
  std::string enum_name;
};

std::vector<FsmConcatInfo> CollectConcatPragmas(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  std::vector<FsmConcatInfo> out;
  for (const auto& p : lexer.FsmConcatPragmas()) {
    FsmConcatInfo info;
    for (const auto& s : p.signal_names) {
      info.signals.push_back(std::string(s));
    }
    info.fsm_name = std::string(p.fsm_name);
    info.enum_name = std::string(p.enum_name);
    out.push_back(info);
  }
  return out;
}

TEST(FsmOneLineCommentPragmaLexing, RecognizedInBothBlockAndOneLineComments) {
  const std::string kSrc =
      "module fsm;\n"
      "  parameter [1:0] // tool enum myFSM\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "  parameter [1:0] /* tool enum myFSM */\n"
      "    T0 = 0, t1 = 1, t2 = 2, t3 = 3;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 2u);
  for (const auto& p : pragmas) {
    EXPECT_EQ(p.form, "enum_only");
    EXPECT_TRUE(p.has_enum);
    EXPECT_EQ(p.enum_name, "myFSM");
    EXPECT_TRUE(p.signal.empty());
  }

  auto idents = CollectIdentifiers(kSrc);
  std::vector<std::string> states;
  for (const auto& id : idents) {
    if (id == "S0" || id == "s1" || id == "s2" || id == "s3") {
      states.push_back(id);
    }
  }
  ASSERT_EQ(states.size(), 4u);
  EXPECT_EQ(states[0], "S0");
  EXPECT_EQ(states[3], "s3");
}

TEST(FsmOneLineCommentPragmaLexing,
     RecognizesStateVectorCurrentStatePragmaInOneLineComment) {
  const std::string kSrc =
      "module fsm;\n"
      "  // tool state_vector cs enum myFSM\n"
      "  logic [1:0] cs;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cs");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "myFSM");
}

TEST(FsmOneLineCommentPragmaLexing,
     RecognizesPartSelectPragmaInOneLineComment) {
  const std::string kSrc =
      "module fsm;\n"
      "  // tool state_vector st[1:0] myFSM enum E\n"
      "  logic [3:0] st;\n"
      "endmodule\n";

  auto part_selects = CollectPartSelectPragmas(kSrc);
  ASSERT_EQ(part_selects.size(), 1u);
  EXPECT_EQ(part_selects[0].signal, "st");
  EXPECT_EQ(part_selects[0].msb, 1);
  EXPECT_EQ(part_selects[0].lsb, 0);
  EXPECT_EQ(part_selects[0].fsm_name, "myFSM");
  EXPECT_EQ(part_selects[0].enum_name, "E");
}

TEST(FsmOneLineCommentPragmaLexing,
     RecognizesConcatenationPragmaInOneLineComment) {
  const std::string kSrc =
      "module fsm;\n"
      "  // tool state_vector {hi , lo} myFSM enum E\n"
      "  logic hi, lo;\n"
      "endmodule\n";

  auto concats = CollectConcatPragmas(kSrc);
  ASSERT_EQ(concats.size(), 1u);
  ASSERT_EQ(concats[0].signals.size(), 2u);
  EXPECT_EQ(concats[0].signals[0], "hi");
  EXPECT_EQ(concats[0].signals[1], "lo");
  EXPECT_EQ(concats[0].fsm_name, "myFSM");
  EXPECT_EQ(concats[0].enum_name, "E");
}

TEST(FsmOneLineCommentPragmaLexing,
     RecognizesOneLineCommentPragmaTerminatedByEndOfFile) {
  const std::string kSrc = "logic [1:0] cs; // tool enum myFSM";

  auto pragmas = CollectFsmPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "myFSM");
  EXPECT_TRUE(pragmas[0].signal.empty());
}

TEST(FsmOneLineCommentPragmaLexing, TheOneLineFormStandsWhereTheBlockFormDoes) {
  const std::string kOneLine =
      "module fsm;\n"
      "  parameter OTHER = 9;\n"
      "  parameter [1:0] // tool enum myFSM\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "endmodule\n";
  const std::string kBlock =
      "module fsm;\n"
      "  parameter OTHER = 9;\n"
      "  parameter [1:0] /* tool enum myFSM */\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "endmodule\n";
  const std::vector<std::string> kPossibleStates = {"S0", "s1", "s2", "s3"};

  EXPECT_EQ(KindBeforeEnumPragma(kOneLine), TokenKind::kRBracket);
  EXPECT_EQ(NamesFollowingEnumPragma(kOneLine), kPossibleStates);

  EXPECT_EQ(KindBeforeEnumPragma(kBlock), KindBeforeEnumPragma(kOneLine));
  EXPECT_EQ(NamesFollowingEnumPragma(kBlock),
            NamesFollowingEnumPragma(kOneLine));
}

TEST(FsmOneLineCommentPragmaLexing,
     ProhibitedSelectIsReportedFromAOneLineComment) {
  const std::string kSrc =
      "module fsm;\n"
      "  logic [3:0] wide;\n"
      "  logic bit_lo;\n"
      "  // tool state_vector {wide[3:0], bit_lo} one_line_fsm enum line_e\n"
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
      LineHolding(kSrc, "// tool state_vector"), "40.4.3"));
}

}  // namespace
