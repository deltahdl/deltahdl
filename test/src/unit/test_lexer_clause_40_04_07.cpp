#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

// §40.4.7 — Pragmas in one-line comments.
//
// The FSM recognition pragmas described throughout §40.4 are not confined to
// block comments. They work in both forms of comment: between the `/*` and `*/`
// delimiters of a block comment, and following the `//` of a one-line comment.
// The LRM's example places the enumeration-name pragma in a one-line comment
// after a parameter bit width:
//
//     parameter [1:0] // tool enum enumeration_name
//     S0 = 0, s1 = 1, s2 = 2, s3 = 3;
//
// Until now the lexer recognized these pragmas only inside block comments and
// discarded the body of every one-line comment. These tests observe that the
// same recognizer now runs over `//` comment bodies, so every §40.4 pragma form
// — the enum-only form, the current-state signal form, and the part-select
// form — is surfaced when written in a one-line comment, exactly as it is in a
// block comment.

namespace {

// Plain-data copy of a recognized current-state / enum-only FSM pragma so
// assertions do not depend on string_views into a transient SourceManager.
struct FsmPragmaInfo {
  std::string form;
  std::string signal;
  std::string enum_name;
  bool has_enum = false;
};

std::vector<FsmPragmaInfo> CollectFsmPragmas(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  std::vector<FsmPragmaInfo> out;
  for (const auto& p : lexer.FsmStatePragmas()) {
    out.push_back(
        {p.form == Lexer::FsmStatePragma::Form::kStateVector ? "state_vector"
                                                             : "enum_only",
         std::string(p.signal_name), std::string(p.enum_name), p.has_enum});
  }
  return out;
}

// Plain-data copy of a recognized part-select (§40.4.2) FSM pragma.
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

// Plain-data copy of a recognized concatenation (§40.4.3) FSM pragma.
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

std::vector<std::string> CollectIdentifiers(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  std::vector<std::string> out;
  for (const auto& t : tokens) {
    if (t.kind == TokenKind::kIdentifier) {
      out.push_back(std::string(t.text));
    }
  }
  return out;
}

// The core §40.4.7 claim — these pragmas work in both block comments and
// one-line comments. The same enum-only pragma is written once in each comment
// style in one source. Both are surfaced identically, confirming the one-line
// form is recognized rather than discarded. The one-line form is the LRM's own
// example (after a parameter bit width), and its state-naming parameters still
// reach the token stream for a downstream extractor to read.
TEST(FsmOneLineCommentPragmaLexing, RecognizedInBothBlockAndOneLineComments) {
  const std::string src =
      "module fsm;\n"
      "  parameter [1:0] // tool enum myFSM\n"
      "    S0 = 0, s1 = 1, s2 = 2, s3 = 3;\n"
      "  parameter [1:0] /* tool enum myFSM */\n"
      "    T0 = 0, t1 = 1, t2 = 2, t3 = 3;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  ASSERT_EQ(pragmas.size(), 2u);
  for (const auto& p : pragmas) {
    EXPECT_EQ(p.form, "enum_only");
    EXPECT_TRUE(p.has_enum);
    EXPECT_EQ(p.enum_name, "myFSM");
    EXPECT_TRUE(p.signal.empty());
  }

  // The one-line comment ends at the newline: the parameters on the following
  // line are ordinary tokens, not swallowed by the comment.
  auto idents = CollectIdentifiers(src);
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

// The current-state signal pragma (§40.4.1's `tool state_vector signal enum E`)
// is one of "these pragmas," so it too is recognized in a one-line comment.
TEST(FsmOneLineCommentPragmaLexing,
     RecognizesStateVectorCurrentStatePragmaInOneLineComment) {
  const std::string src =
      "module fsm;\n"
      "  // tool state_vector cs enum myFSM\n"
      "  logic [1:0] cs;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cs");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "myFSM");
}

// The part-select pragma form (§40.4.2) is likewise recognized in a one-line
// comment, confirming the breadth of "these pragmas" carries into the `//`
// comment path and not just the enum-only form of the LRM example.
TEST(FsmOneLineCommentPragmaLexing,
     RecognizesPartSelectPragmaInOneLineComment) {
  const std::string src =
      "module fsm;\n"
      "  // tool state_vector st[1:0] myFSM enum E\n"
      "  logic [3:0] st;\n"
      "endmodule\n";

  auto part_selects = CollectPartSelectPragmas(src);
  ASSERT_EQ(part_selects.size(), 1u);
  EXPECT_EQ(part_selects[0].signal, "st");
  EXPECT_EQ(part_selects[0].msb, 1);
  EXPECT_EQ(part_selects[0].lsb, 0);
  EXPECT_EQ(part_selects[0].fsm_name, "myFSM");
  EXPECT_EQ(part_selects[0].enum_name, "E");
}

// The concatenation pragma form (§40.4.3) completes the set of §40.4 pragma
// families, and it too is recognized in a one-line comment. This confirms that
// the `//` comment path feeds the shared recognizer for every pragma form, not
// just the enum-only, current-state, and part-select forms above.
TEST(FsmOneLineCommentPragmaLexing,
     RecognizesConcatenationPragmaInOneLineComment) {
  const std::string src =
      "module fsm;\n"
      "  // tool state_vector {hi , lo} myFSM enum E\n"
      "  logic hi, lo;\n"
      "endmodule\n";

  auto concats = CollectConcatPragmas(src);
  ASSERT_EQ(concats.size(), 1u);
  ASSERT_EQ(concats[0].signals.size(), 2u);
  EXPECT_EQ(concats[0].signals[0], "hi");
  EXPECT_EQ(concats[0].signals[1], "lo");
  EXPECT_EQ(concats[0].fsm_name, "myFSM");
  EXPECT_EQ(concats[0].enum_name, "E");
}

// Edge case — a one-line comment is terminated by end of file rather than a
// newline. The comment is the last thing in the source and has no trailing
// newline, so the lexer's line-comment scan stops at end of file. The pragma
// body still reaches the recognizer and the pragma is surfaced, exercising the
// end-of-file termination of the line-comment scan rather than the newline one.
TEST(FsmOneLineCommentPragmaLexing,
     RecognizesOneLineCommentPragmaTerminatedByEndOfFile) {
  const std::string src = "logic [1:0] cs; // tool enum myFSM";

  auto pragmas = CollectFsmPragmas(src);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "enum_only");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "myFSM");
  EXPECT_TRUE(pragmas[0].signal.empty());
}

}  // namespace
