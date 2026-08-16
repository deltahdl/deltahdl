#pragma once

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

struct LexOneResult {
  SourceManager mgr;
  Token token;
};

inline LexOneResult LexOne(const std::string& src) {
  LexOneResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  result.token = lexer.Next();
  return result;
}

struct LexAllResult {
  std::vector<Token> tokens;
  bool has_errors;
};

// Pass TextOrigin::kPreprocessorOutput for a src that hand-writes a
// kKeywordMarker byte: such a test stands in for the Preprocessor and has to
// say so, because a marker in text the Preprocessor did not produce is a byte
// the user wrote, which the Lexer reports as an unexpected character.
inline std::vector<Token> Lex(const std::string& src,
                              TextOrigin origin = TextOrigin::kUserSource) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag, origin);
  return lexer.LexAll();
}

// Every diagnostic lexing a source reported, in the order it was reported. A
// test asserting that one rule of IEEE 1800-2023 was enforced rather than
// another reads the clause here, which the bool LexWithDiag() returns cannot
// distinguish: every rejection sets that same flag.
inline std::vector<Diagnostic> LexDiagnostics(const std::string& src) {
  // Static for the same reason LexWithDiag() below is: a Diagnostic holds its
  // own message, but the Lexer reads a string_view into the manager's buffer
  // for as long as it runs.
  static SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  return diag.Diagnostics();
}

inline LexAllResult LexWithDiag(const std::string& src) {
  // Keep the SourceManager alive for the whole test process (as Lex() does):
  // Token::text is a string_view into the manager's file buffer, so a local
  // manager would leave every returned token dangling once this call returns.
  static SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  return {tokens, diag.HasErrors()};
}
