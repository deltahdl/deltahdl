#pragma once

#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

// The terminal classes of the VCD file grammars, as the standard spells them.
//
// §21.7.2's Syntax 21-20 defines the 4-state dump file and §21.7.4's Syntax
// 21-27 the extended one. The two are separate productions, but the extended
// file admits the 4-state constructs by name equivalence -- a construct name
// that matches a 4-state one means the same thing there -- so the terminals
// below belong to both. Each grammar's own top production, and the terminals
// only it defines, stay with the subclause that states them.
//
// Every production these check is white-space-insensitive, so a validator
// works from the token stream and never needs line or column information.

// identifier_code, scope_identifier, comment_text and their relatives: one or
// more ASCII characters, and printable ones (! to ~, decimal 33 to 126) at
// that, which is the charset rule the prose adds to the grammar.
inline bool IsPrintableAscii(const std::string& t) {
  if (t.empty()) return false;
  for (unsigned char c : t) {
    if (c < 33 || c > 126) return false;
  }
  return true;
}

// decimal_number ::= {decimal_digit}.
inline bool IsDecimal(const std::string& t) {
  if (t.empty()) return false;
  for (char c : t) {
    if (c < '0' || c > '9') return false;
  }
  return true;
}

// value ::= 0 | 1 | x | X | z | Z.
inline bool IsValueChar(char c) { return std::strchr("01xXzZ", c) != nullptr; }

// binary_number digits of a b-form vector_value_change: 4-state digits.
inline bool IsFourStateDigits(const std::string& t) {
  if (t.empty()) return false;
  for (char c : t) {
    if (!IsValueChar(c)) return false;
  }
  return true;
}

// scope_type ::= begin | fork | function | module | task.
inline bool IsScopeType(const std::string& t) {
  static const char* kinds[] = {"begin", "fork", "function", "module", "task"};
  for (const char* k : kinds) {
    if (t == k) return true;
  }
  return false;
}

// var_type: the eighteen keywords a 4-state $var construct may carry.
inline bool IsFourStateVarType(const std::string& t) {
  static const char* types[] = {
      "event",   "integer", "parameter", "real", "realtime", "reg",
      "supply0", "supply1", "time",      "tri",  "triand",   "trior",
      "trireg",  "tri0",    "tri1",      "wand", "wire",     "wor"};
  for (const char* k : types) {
    if (t == k) return true;
  }
  return false;
}

// A $timescale body: time_number (1 | 10 | 100) followed by time_unit
// (s | ms | us | ns | ps | fs), which the file may write with or without
// white space between them, so a caller joins the body's tokens first.
inline bool IsTimescaleBody(const std::string& body) {
  static const char* nums[] = {"100", "10", "1"};  // longest match first
  static const char* units[] = {"ms", "us", "ns", "ps", "fs", "s"};
  for (const char* n : nums) {
    if (body.rfind(n, 0) != 0) continue;
    std::string rest = body.substr(std::strlen(n));
    for (const char* u : units) {
      if (rest == u) return true;
    }
  }
  return false;
}

// Consumes the 4-state value_change at toks[i], advancing i past it. A
// scalar_value_change is a single token -- a value character immediately
// followed by the identifier code -- while a vector_value_change is a
// base-letter token (b or B plus binary digits, or r or R plus a real number)
// followed by the identifier code as a token of its own.
//
// Returns "" when one was consumed and a description of the violation
// otherwise. `handled` comes back false when the token opens none of these
// forms, which is not itself an error: a grammar that defines a value change
// form of its own takes over from there, and one that does not reports the
// token as no simulation command at all.
inline std::string ConsumeFourStateValueChange(
    const std::vector<std::string>& toks, size_t& i, bool& handled) {
  handled = true;
  const std::string& t = toks[i];
  if (IsValueChar(t[0])) {
    if (t.size() < 2 || !IsPrintableAscii(t.substr(1))) {
      return "malformed scalar_value_change: " + t;
    }
    ++i;
    return "";
  }
  if (t[0] == 'b' || t[0] == 'B') {
    if (t.size() < 2 || !IsFourStateDigits(t.substr(1))) {
      return "malformed b-form vector_value_change: " + t;
    }
    if (i + 1 >= toks.size() || !IsPrintableAscii(toks[i + 1])) {
      return "b-form value without identifier code: " + t;
    }
    i += 2;
    return "";
  }
  if (t[0] == 'r' || t[0] == 'R') {
    if (t.size() < 2) return "empty r-form real number";
    char* endp = nullptr;
    std::strtod(t.c_str() + 1, &endp);
    if (endp != t.c_str() + t.size()) {
      return "malformed r-form real number: " + t;
    }
    if (i + 1 >= toks.size() || !IsPrintableAscii(toks[i + 1])) {
      return "r-form value without identifier code: " + t;
    }
    i += 2;
    return "";
  }
  handled = false;
  return "";
}

// The identifier codes the file's $var commands declare, in the order the
// declarations appear.
inline std::vector<std::string> CollectVarCodes(
    const std::vector<std::string>& toks) {
  std::vector<std::string> codes;
  for (size_t i = 0; i + 4 < toks.size(); ++i) {
    if (toks[i] == "$var") codes.push_back(toks[i + 3]);
  }
  return codes;
}

// Whether no token fuses two commands together. A '$' introduces a keyword
// command, so once the file is split on white space it can only appear at the
// start of a token; a writer that ran two commands together -- $end
// immediately followed by the next keyword, say, or a value change flushed
// against $end -- leaves a token with an interior '$'.
inline bool NoFusedCommands(const std::vector<std::string>& toks) {
  for (const auto& t : toks) {
    if (t.find('$', 1) != std::string::npos) return false;
  }
  return true;
}
