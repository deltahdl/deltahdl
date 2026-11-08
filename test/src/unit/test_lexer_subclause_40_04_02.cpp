#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

struct PartSelectPragmaInfo {
  std::string signal;
  int msb = 0;
  int lsb = 0;
  std::string fsm_name;
  std::string enum_name;
};

std::vector<PartSelectPragmaInfo> CollectPartSelectPragmas(
    const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  std::vector<PartSelectPragmaInfo> out;
  for (const auto& p : lexer.FsmPartSelectPragmas()) {
    out.push_back({std::string(p.signal_name), p.msb, p.lsb,
                   std::string(p.fsm_name), std::string(p.enum_name)});
  }
  return out;
}

TEST(FsmPartSelectPragmaLexing, RecognizesPartSelectPragma) {
  auto pragmas = CollectPartSelectPragmas(
      "/* tool state_vector cur_state[3:0] my_fsm "
      "enum state_e */");
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_EQ(pragmas[0].msb, 3);
  EXPECT_EQ(pragmas[0].lsb, 0);
  EXPECT_EQ(pragmas[0].fsm_name, "my_fsm");
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

TEST(FsmPartSelectPragmaLexing, MalformedPartSelectRangeIsNotRecognized) {
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool state_vector cur_state[3] my_fsm enum "
                               "state_e */")
          .empty());
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool state_vector cur_state[hi:lo] my_fsm "
                               "enum state_e */")
          .empty());
}

TEST(FsmPartSelectPragmaLexing, FsmNameIsRequired) {
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool state_vector cur_state[3:0] enum "
                               "state_e */")
          .empty());
}

TEST(FsmPartSelectPragmaLexing, RequiresLiteralEnumKeywordInBinding) {
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool state_vector cur_state[3:0] my_fsm "
                               "uses state_e */")
          .empty());
}

TEST(FsmPartSelectPragmaLexing, RequiresToolAndStateVectorKeywords) {
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* state_vector cur_state[3:0] my_fsm enum "
                               "state_e */")
          .empty());
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool vector cur_state[3:0] my_fsm enum "
                               "state_e */")
          .empty());
}

TEST(FsmPartSelectPragmaLexing, RecognizedWithinModuleBody) {
  const std::string kSrc =
      "module fsm;\n"
      "  logic [7:0] bus;\n"
      "  /* tool state_vector bus[3:0] my_fsm enum state_e */\n"
      "endmodule\n";
  auto pragmas = CollectPartSelectPragmas(kSrc);
  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "bus");
  EXPECT_EQ(pragmas[0].msb, 3);
  EXPECT_EQ(pragmas[0].lsb, 0);
  EXPECT_EQ(pragmas[0].fsm_name, "my_fsm");
}

TEST(FsmPartSelectPragmaLexing, PartSelectIsSeparateFromSimpleSignalPragma) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  const std::string kSrc =
      "/* tool state_vector cur_state[3:0] my_fsm enum e */";
  auto fid = mgr.AddFile("<test>", kSrc);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_EQ(lexer.FsmPartSelectPragmas().size(), 1u);
  EXPECT_TRUE(lexer.FsmStatePragmas().empty());

  SourceManager mgr2;
  DiagEngine diag2(mgr2);
  const std::string kSimple = "/* tool state_vector cur_state enum e */";
  auto fid2 = mgr2.AddFile("<test>", kSimple);
  Lexer lexer2(mgr2.FileContent(fid2), fid2, diag2);
  lexer2.LexAll();
  EXPECT_TRUE(lexer2.FsmPartSelectPragmas().empty());
  EXPECT_EQ(lexer2.FsmStatePragmas().size(), 1u);
}

TEST(FsmPartSelectPragmaLexing, BoundsTooLargeForAnIndexAreNotRecognized) {
  EXPECT_TRUE(CollectPartSelectPragmas(
                  "/* tool state_vector cs[4294967296:0] my_fsm enum e */")
                  .empty());
  EXPECT_TRUE(CollectPartSelectPragmas(
                  "/* tool state_vector cs[3:99999999999] my_fsm enum e */")
                  .empty());

  auto held = CollectPartSelectPragmas(
      "/* tool state_vector cs[2147483647:0] my_fsm enum e */");
  ASSERT_EQ(held.size(), 1u);
  EXPECT_EQ(held[0].msb, 2147483647);
  EXPECT_EQ(held[0].lsb, 0);
}

TEST(FsmPartSelectPragmaLexing, OperandNotShapedAsAPartSelectIsNotRecognized) {
  for (const char* operand : {"cur.state", "[3:0]", "cur_state[3:0",
                              "9cur[3:0]", "cur_state[:0]", "cur_state[3:]"}) {
    EXPECT_TRUE(CollectPartSelectPragmas(std::string("/* tool state_vector ") +
                                         operand + " my_fsm enum state_e */")
                    .empty())
        << operand;
  }
}

TEST(FsmPartSelectPragmaLexing, MissingOrMalformedNamesAreNotRecognized) {
  EXPECT_TRUE(
      CollectPartSelectPragmas("/* tool state_vector cur_state[3:0] enum e */")
          .empty());
  EXPECT_TRUE(CollectPartSelectPragmas(
                  "/* tool state_vector cur_state[3:0] 9fsm enum state_e */")
                  .empty());
  EXPECT_TRUE(CollectPartSelectPragmas(
                  "/* tool state_vector cur_state[3:0] my_fsm enum 9e */")
                  .empty());
}

}  // namespace
