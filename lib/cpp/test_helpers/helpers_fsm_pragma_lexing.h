#pragma once

#include <cstddef>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "lexer/token.h"

using namespace delta;

struct FsmPragmaInfo {
  std::string form;
  std::string signal;
  std::string enum_name;
  bool has_enum = false;
};

inline std::vector<FsmPragmaInfo> CollectFsmPragmas(const std::string& src) {
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

inline std::vector<std::string> CollectIdentifiers(const std::string& src) {
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

inline bool IsAfter(SourceLoc loc, SourceLoc other) {
  return loc.line > other.line ||
         (loc.line == other.line && loc.column > other.column);
}

inline SourceLoc EnumPragmaLocAt(const Lexer& lexer, size_t index) {
  size_t seen = 0;
  for (const auto& p : lexer.FsmStatePragmas()) {
    if (p.form != Lexer::FsmStatePragma::Form::kEnumOnly) {
      continue;
    }
    if (seen == index) {
      return p.loc;
    }
    ++seen;
  }
  return SourceLoc();
}

inline std::vector<std::string> NamesFollowingEnumPragma(const std::string& src,
                                                         size_t index = 0) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  SourceLoc pragma_loc = EnumPragmaLocAt(lexer, index);

  size_t i = 0;
  while (i < tokens.size() && !IsAfter(tokens[i].loc, pragma_loc)) {
    ++i;
  }
  std::vector<std::string> names;
  for (; i < tokens.size(); ++i) {
    if (tokens[i].kind == TokenKind::kSemicolon) {
      break;
    }
    if (tokens[i].kind == TokenKind::kIdentifier) {
      names.push_back(std::string(tokens[i].text));
    }
  }
  return names;
}

inline TokenKind KindBeforeEnumPragma(const std::string& src,
                                      size_t index = 0) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  SourceLoc pragma_loc = EnumPragmaLocAt(lexer, index);

  TokenKind before = TokenKind::kEof;
  for (const auto& t : tokens) {
    if (IsAfter(t.loc, pragma_loc)) {
      break;
    }
    before = t.kind;
  }
  return before;
}
