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

inline std::vector<Token> Lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
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
