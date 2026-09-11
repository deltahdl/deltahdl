#pragma once

#include <cstddef>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

// Plain-data copy of a recognized §40.4.1 FSM pragma so that assertions do not
// depend on string_views that point into a transient SourceManager.
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

// Whether `loc` stands after `other` in the same source.
inline bool IsAfter(SourceLoc loc, SourceLoc other) {
  return loc.line > other.line ||
         (loc.line == other.line && loc.column > other.column);
}

// Where the first enum-only FSM pragma of a lexed source stands. §40.4.4
// through §40.4.6 each place that pragma against something - a signal
// declaration, a multi-signal one, a parameter - and say what follows it, so
// its location is what a case reads to apply the rule to the source it wrote
// rather than to a list of names it already knew.
inline SourceLoc FirstEnumPragmaLoc(const Lexer& lexer) {
  for (const auto& p : lexer.FsmStatePragmas()) {
    if (p.form == Lexer::FsmStatePragma::Form::kEnumOnly) {
      return p.loc;
    }
  }
  return SourceLoc();
}

// The names declared after the first enum-only pragma of `src`, in order, as
// far as the semicolon that ends the declaration the pragma sits in. §40.4.5's
// first and next signal and §40.4.6's possible states are read from this list.
inline std::vector<std::string> NamesFollowingEnumPragma(
    const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  SourceLoc pragma_loc = FirstEnumPragmaLoc(lexer);

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

// The kind of the last token standing before the first enum-only pragma of
// `src`, which is what §40.4.6's placement rule is about: the pragma goes
// immediately after the `parameter` keyword, or immediately after the bit width
// where one is used.
inline TokenKind KindBeforeEnumPragma(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  SourceLoc pragma_loc = FirstEnumPragmaLoc(lexer);

  TokenKind before = TokenKind::kEof;
  for (const auto& t : tokens) {
    if (IsAfter(t.loc, pragma_loc)) {
      break;
    }
    before = t.kind;
  }
  return before;
}
