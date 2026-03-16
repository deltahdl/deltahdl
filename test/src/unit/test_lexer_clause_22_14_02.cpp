#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1364_1995_ModuleIsKeyword) {
  auto kw = LookupKeyword("module", KeywordVersion::kVer13641995);
  EXPECT_EQ(kw, std::optional(TokenKind::kKwModule));
}

TEST(Lexer, KeywordVersion_1364_1995_AutomaticIsNotKeyword) {
  auto kw = LookupKeyword("automatic", KeywordVersion::kVer13641995);
  EXPECT_FALSE(kw.has_value());
}

TEST(Lexer, KeywordVersion_1364_1995_AllKeywordsRecognized) {
  const char* kTable22_1[] = {
      "always",    "and",        "assign",      "begin",
      "buf",       "bufif0",     "bufif1",      "case",
      "casex",     "casez",      "cmos",        "deassign",
      "default",   "defparam",   "disable",     "edge",
      "else",      "end",        "endcase",     "endfunction",
      "endmodule", "endprimitive", "endspecify", "endtable",
      "endtask",   "event",      "for",         "force",
      "forever",   "fork",       "function",    "highz0",
      "highz1",    "if",         "ifnone",      "initial",
      "inout",     "input",      "integer",     "join",
      "large",     "macromodule", "medium",     "module",
      "nand",      "negedge",    "nmos",        "nor",
      "not",       "notif0",     "notif1",      "or",
      "output",    "parameter",  "pmos",        "posedge",
      "primitive", "pull0",      "pull1",       "pulldown",
      "pullup",    "rcmos",      "real",        "realtime",
      "reg",       "release",    "repeat",      "rnmos",
      "rpmos",     "rtran",      "rtranif0",    "rtranif1",
      "scalared",  "small",      "specify",     "specparam",
      "strong0",   "strong1",    "supply0",     "supply1",
      "table",     "task",       "time",        "tran",
      "tranif0",   "tranif1",    "tri",         "tri0",
      "tri1",      "triand",     "trior",       "trireg",
      "vectored",  "wait",       "wand",        "weak0",
      "weak1",     "while",      "wire",        "wor",
      "xnor",      "xor",
  };
  for (const char* kw : kTable22_1) {
    auto result = LookupKeyword(kw, KeywordVersion::kVer13641995);
    EXPECT_TRUE(result.has_value()) << kw << " should be a keyword in 1364-1995";
  }
}

TEST(Lexer, KeywordVersion_1364_1995_LaterKeywordsNotRecognized) {
  // 1364-2001 additions
  EXPECT_FALSE(
      LookupKeyword("automatic", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("cell", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("config", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("generate", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("genvar", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("localparam", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("signed", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("unsigned", KeywordVersion::kVer13641995).has_value());
  // 1364-2005 addition
  EXPECT_FALSE(
      LookupKeyword("uwire", KeywordVersion::kVer13641995).has_value());
  // 1800-2005 additions
  EXPECT_FALSE(
      LookupKeyword("logic", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("bit", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("interface", KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(
      LookupKeyword("class", KeywordVersion::kVer13641995).has_value());
  // 1800-2009 addition
  EXPECT_FALSE(
      LookupKeyword("checker", KeywordVersion::kVer13641995).has_value());
}

TEST(Lexer, KeywordVersion_1364_1995_NonKeywordIdentifier) {
  auto kw = LookupKeyword("my_signal", KeywordVersion::kVer13641995);
  EXPECT_FALSE(kw.has_value());
}

}  // namespace
