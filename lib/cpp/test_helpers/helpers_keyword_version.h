#pragma once

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "lexer/lexer.h"
#include "lexer/token.h"

inline std::string In(const char* spec, const std::string& body) {
  return std::string("`begin_keywords \"") + spec + "\"\n" + body +
         "`end_keywords\n";
}

inline std::string In1995(const std::string& body) {
  return In("1364-1995", body);
}
inline std::string In2001(const std::string& body) {
  return In("1364-2001", body);
}
inline std::string InNoconfig(const std::string& body) {
  return In("1364-2001-noconfig", body);
}
inline std::string In2005(const std::string& body) {
  return In("1364-2005", body);
}
inline std::string InSv2005(const std::string& body) {
  return In("1800-2005", body);
}
inline std::string InSv2009(const std::string& body) {
  return In("1800-2009", body);
}
inline std::string InSv2012(const std::string& body) {
  return In("1800-2012", body);
}

inline uint32_t LineInRegion(uint32_t body_line) {
  static constexpr char kBodyMark[] = "\x02";
  const std::string kWrapped = In("", kBodyMark);
  const std::string kAbove = kWrapped.substr(0, kWrapped.find(kBodyMark));
  const auto kDirectiveLines =
      static_cast<uint32_t>(std::count(kAbove.begin(), kAbove.end(), '\n'));
  return kDirectiveLines + body_line;
}

inline std::string VarDecl(const char* word) {
  return std::string("module m;\n  reg [7:0] ") + word + ";\nendmodule\n";
}

inline TokenKind KindInRegion(const std::string& version,
                              const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"" + version + "\"\n" + word + "\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors()) << version << " / " << word;

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == word) return tok.kind;
  }
  ADD_FAILURE() << word << " never reached the token stream";
  return TokenKind::kError;
}

inline TokenKind KindAfterSpecifier(const std::string& spec,
                                    const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"" + spec + "\"\n" + word + "\n`end_keywords\n", f);
  static_cast<void>(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == word) return tok.kind;
  }
  ADD_FAILURE() << word << " never reached the token stream";
  return TokenKind::kError;
}
