#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_fsm_pragma_lexing.h"
#include "lexer/lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(FsmStatePragmaLexing, RecognizesCurrentStatePragma) {
  auto pragmas = CollectFsmPragmas("/* tool state_vector cur_state */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_FALSE(pragmas[0].has_enum);
}

TEST(FsmStatePragmaLexing, RecognizesCombinedEnumPragma) {
  auto pragmas =
      CollectFsmPragmas("/* tool state_vector cur_state enum state_e */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

TEST(FsmStatePragmaLexing, RequiresToolKeyword) {
  EXPECT_TRUE(CollectFsmPragmas("/* state_vector cur_state */").empty());
  EXPECT_TRUE(CollectFsmPragmas("/* just an ordinary comment */").empty());
}

TEST(FsmStatePragmaLexing, RequiresStateVectorKeyword) {
  EXPECT_TRUE(CollectFsmPragmas("/* tool vector cur_state */").empty());
}

TEST(FsmStatePragmaLexing, EnumKeywordRequiredToBindName) {
  EXPECT_TRUE(
      CollectFsmPragmas("/* tool state_vector cur_state state_e */").empty());
  auto bound =
      CollectFsmPragmas("/* tool state_vector cur_state enum state_e */");
  ASSERT_EQ(bound.size(), 1u);
  EXPECT_TRUE(bound[0].has_enum);
}

TEST(FsmStatePragmaLexing, PragmaWithinModuleBody) {
  const std::string kSrc =
      "module fsm;\n"
      "  logic [2:0] cur_state;\n"
      "  /* tool state_vector cur_state enum state_e */\n"
      "endmodule\n";
  auto pragmas = CollectFsmPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

TEST(FsmStatePragmaLexing, SeparatePragmaInDeclarationIsInvisibleToTokens) {
  const std::string kSrc = "logic [7:0] /* tool enum state_e */ cur_state;";

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", kSrc);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();

  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLogic);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBracket);
  EXPECT_EQ(tokens[6].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].text, "cur_state");

  ASSERT_EQ(lexer.FsmStatePragmas().size(), 1u);
  EXPECT_EQ(lexer.FsmStatePragmas()[0].form,
            Lexer::FsmStatePragma::Form::kEnumOnly);
  EXPECT_EQ(lexer.FsmStatePragmas()[0].enum_name, "state_e");
}

TEST(FsmStatePragmaLexing, SeparateEnumPragmaPairsWithStateVectorPragma) {
  const std::string kSrc =
      "module fsm;\n"
      "  /* tool state_vector cur_state */\n"
      "  logic [2:0] /* tool enum state_e */ cur_state;\n"
      "endmodule\n";
  auto pragmas = CollectFsmPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 2u);

  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_FALSE(pragmas[0].has_enum);

  EXPECT_EQ(pragmas[1].form, "enum_only");
  EXPECT_TRUE(pragmas[1].has_enum);
  EXPECT_EQ(pragmas[1].enum_name, "state_e");
}

TEST(FsmStatePragmaLexing, IncompletePragmasAreNotRecognized) {
  EXPECT_TRUE(CollectFsmPragmas("/* tool */").empty());
  EXPECT_TRUE(CollectFsmPragmas("/* tool state_vector */").empty());
  EXPECT_TRUE(CollectFsmPragmas("/* tool enum */").empty());
}

TEST(FsmStatePragmaLexing, IgnoresPartSelectAndConcatenationForms) {
  EXPECT_TRUE(
      CollectFsmPragmas("/* tool state_vector cur_state[1:0] fsm enum e */")
          .empty());
  EXPECT_TRUE(
      CollectFsmPragmas("/* tool state_vector {hi, lo} fsm enum e */").empty());
}

TEST(FsmStatePragmaLexing, NamesMayCarryDollarSignsAsIdentifiersDo) {
  auto pragmas = CollectFsmPragmas("/* tool state_vector n$657 enum e$num */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "n$657");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "e$num");
}

TEST(FsmStatePragmaLexing, NamesMayNotOpenWithADigitOrDollarSign) {
  EXPECT_TRUE(CollectFsmPragmas("/* tool state_vector $state */").empty());
  EXPECT_TRUE(CollectFsmPragmas("/* tool state_vector 1state */").empty());
  EXPECT_TRUE(
      CollectFsmPragmas("/* tool state_vector cur_state enum $e */").empty());
}

TEST(FsmStatePragmaLexing,
     KeywordAloneOrTrailingWordsOtherThanEnumAreNotAPragma) {
  EXPECT_TRUE(CollectFsmPragmas("/* tool */").empty());
  EXPECT_TRUE(
      CollectFsmPragmas("/* tool state_vector cur_state with state_e */")
          .empty());
}

TEST(FsmStatePragmaLexing, NamesAreSimpleIdentifiers) {
  auto pragmas = CollectFsmPragmas("/* tool state_vector _cur$state */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "_cur$state");
  EXPECT_TRUE(CollectFsmPragmas("/* tool enum 9e */").empty());
}

TEST(FsmStatePragmaLexing, TwoPragmasOnOneLineAreBothRecorded) {
  auto pragmas =
      CollectFsmPragmas("/* tool enum first_e */ /* tool enum second_e */");
  ASSERT_EQ(pragmas.size(), 2u);
  EXPECT_EQ(pragmas[0].enum_name, "first_e");
  EXPECT_EQ(pragmas[1].enum_name, "second_e");
}

TEST(FsmStatePragmaLexing, CommentReadAgainAfterARewindIsRecordedOnce) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid =
      mgr.AddFile("<test>",
                  "/* tool state_vector cur_state */\n"
                  "// tool state_vector cur[3:0] part_fsm enum part_e\n"
                  "/* tool state_vector {a, b} cat_fsm enum cat_e */\n"
                  "/* tool state_vector {a[1:0], b} sel_fsm enum sel_e */\n"
                  "x\n");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto start = lexer.SavePos();
  lexer.LexAll();
  lexer.RestorePos(start);
  lexer.LexAll();

  EXPECT_EQ(lexer.FsmStatePragmas().size(), 1u);
  EXPECT_EQ(lexer.FsmPartSelectPragmas().size(), 1u);
  EXPECT_EQ(lexer.FsmConcatPragmas().size(), 1u);
  EXPECT_EQ(diag.WarningCount(), 1u);
}

}  // namespace
