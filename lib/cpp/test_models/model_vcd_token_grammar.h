#pragma once

#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <functional>
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

// Consumes the scalar_value_change at toks[i], which is one token: a value
// character immediately followed by the identifier code.
//
// Returns "" when one was consumed and a description of the violation
// otherwise.
inline std::string ConsumeScalarValueChange(
    const std::vector<std::string>& toks, size_t& i) {
  const std::string& t = toks[i];
  if (t.size() < 2 || !IsPrintableAscii(t.substr(1))) {
    return "malformed scalar_value_change: " + t;
  }
  ++i;
  return "";
}

// Consumes the b-form vector_value_change at toks[i]: b or B and the binary
// digits as one token, then the identifier code as a token of its own.
//
// Returns "" when one was consumed and a description of the violation
// otherwise.
inline std::string ConsumeBFormValueChange(const std::vector<std::string>& toks,
                                           size_t& i) {
  const std::string& t = toks[i];
  if (t.size() < 2 || !IsFourStateDigits(t.substr(1))) {
    return "malformed b-form vector_value_change: " + t;
  }
  if (i + 1 >= toks.size() || !IsPrintableAscii(toks[i + 1])) {
    return "b-form value without identifier code: " + t;
  }
  i += 2;
  return "";
}

// Consumes the r-form vector_value_change at toks[i]: r or R and the real
// number as one token, then the identifier code as a token of its own.
//
// Returns "" when one was consumed and a description of the violation
// otherwise.
inline std::string ConsumeRFormValueChange(const std::vector<std::string>& toks,
                                           size_t& i) {
  const std::string& t = toks[i];
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
  if (IsValueChar(t[0])) return ConsumeScalarValueChange(toks, i);
  if (t[0] == 'b' || t[0] == 'B') return ConsumeBFormValueChange(toks, i);
  if (t[0] == 'r' || t[0] == 'R') return ConsumeRFormValueChange(toks, i);
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

// One declaration_command as the file writes it: the keyword that opens it and
// the tokens between that keyword and the $end closing it.
struct VcdDeclarationCommand {
  std::string keyword;
  std::vector<std::string> body;
};

// The declaration command body shapes both dump file grammars fix, whatever
// the grammar in force adds to them: every command's text is printable ASCII,
// a $timescale carries time_number time_unit, and $upscope and $enddefinitions
// carry nothing.
//
// `handled` comes back false for a keyword whose body shape the grammar in
// force states instead, which is not itself an error: the caller checks that
// shape for itself.
//
// Returns "" when the command conforms, else a description of the violation.
inline std::string CheckFixedDeclarationBody(const VcdDeclarationCommand& cmd,
                                             bool& handled) {
  handled = true;
  for (const auto& b : cmd.body) {
    if (!IsPrintableAscii(b)) {
      return cmd.keyword + " body has non-ASCII token: " + b;
    }
  }
  if (cmd.keyword == "$timescale") {
    std::string joined;
    for (const auto& b : cmd.body) joined += b;
    if (!IsTimescaleBody(joined)) {
      return "$timescale body is not time_number time_unit: " + joined;
    }
    return "";
  }
  if (cmd.keyword == "$upscope" || cmd.keyword == "$enddefinitions") {
    if (!cmd.body.empty()) {
      return cmd.keyword + " carries an unexpected body";
    }
    return "";
  }
  handled = false;
  return "";
}

// Consumes the leading run of declaration commands, which is the
// {declaration_command} half of a dump file's top production, advancing i to
// the first token that does not open one.
//
// `opens_a_declaration` decides which keywords belong to that half, since a
// keyword a grammar classes as a declaration command may still be written
// among the simulation commands. Every declaration command is keyword,
// command text, $end, which is checked here; CheckFixedDeclarationBody checks
// the body shapes both grammars fix, and `check_body` states the per-keyword
// shapes the grammar in force defines for the rest.
//
// Returns "" when the run conforms, else a description of the first violation.
inline std::string ConsumeDeclarationCommands(
    const std::vector<std::string>& toks, size_t& i,
    const std::function<bool(const std::string&)>& opens_a_declaration,
    const std::function<std::string(const VcdDeclarationCommand&)>&
        check_body) {
  while (i < toks.size() && opens_a_declaration(toks[i])) {
    VcdDeclarationCommand cmd;
    cmd.keyword = toks[i++];
    while (i < toks.size() && toks[i] != "$end") cmd.body.push_back(toks[i++]);
    if (i >= toks.size()) return cmd.keyword + " not terminated by $end";
    ++i;  // past $end
    bool handled = false;
    std::string err = CheckFixedDeclarationBody(cmd, handled);
    if (!err.empty()) return err;
    if (handled) continue;
    err = check_body(cmd);
    if (!err.empty()) return err;
  }
  return "";
}

// Consumes a checkpoint section -- the keyword at toks[i], the value changes
// inside it, and the $end closing it -- advancing i past that $end.
//
// Returns "" when the section conforms, else a description of the first
// violation.
inline std::string ConsumeCheckpointSection(
    const std::vector<std::string>& toks, size_t& i,
    const std::function<std::string(const std::vector<std::string>&, size_t&)>&
        consume_value_change) {
  const std::string& keyword = toks[i];
  std::string prefix = keyword + " section: ";
  ++i;
  while (i < toks.size() && toks[i] != "$end") {
    std::string err = consume_value_change(toks, i);
    if (!err.empty()) return prefix + err;
  }
  if (i >= toks.size()) return keyword + " not terminated by $end";
  ++i;
  return "";
}

// Consumes the $comment at toks[i] and every token through the $end closing
// it.
//
// Returns "" when it is closed, else a description of the violation.
inline std::string ConsumeComment(const std::vector<std::string>& toks,
                                  size_t& i) {
  ++i;
  while (i < toks.size() && toks[i] != "$end") ++i;
  if (i >= toks.size()) return "$comment not terminated by $end";
  ++i;
  return "";
}

// Consumes the simulation_time at toks[i], which is one token: # followed by a
// decimal_number.
//
// Returns "" when one was consumed, else a description of the violation.
inline std::string ConsumeSimulationTime(const std::vector<std::string>& toks,
                                         size_t& i) {
  const std::string& t = toks[i];
  if (t.size() < 2 || !IsDecimal(t.substr(1))) {
    return "simulation_time is not # decimal_number: " + t;
  }
  ++i;
  return "";
}

// Gives `consume_other` first refusal on the $-keyword at toks[i], for a
// grammar that admits a simulation command of its own. It reports through
// `handled` the way ConsumeFourStateValueChange does, and a grammar defining
// no such command passes no `consume_other`, which handles nothing.
//
// Returns "" when nothing was consumed or the command conforms, else a
// description of the violation.
inline std::string ConsumeOtherSimulationCommand(
    const std::vector<std::string>& toks, size_t& i,
    const std::function<std::string(const std::vector<std::string>&, size_t&,
                                    bool&)>& consume_other,
    bool& handled) {
  handled = false;
  if (!consume_other) return "";
  return consume_other(toks, i, handled);
}

// Consumes the simulation commands that follow, which is the
// {simulation_command} half of the same production, advancing i to the end of
// the stream.
//
// A checkpoint section -- the keyword `opens_a_checkpoint_section` names, its
// value changes, $end -- a $comment, a simulation time, and a bare value
// change are what every dump file's simulation half admits, and
// `consume_value_change` reads one value change in the forms the grammar in
// force defines. `consume_other` gets first refusal on any further $-keyword,
// for a grammar that admits a command of its own here, and a keyword it leaves
// unhandled is a declaration command showing up after the simulation commands
// began, which the top production forbids.
//
// Returns "" when the run conforms, else a description of the first violation.
inline std::string ConsumeSimulationCommands(
    const std::vector<std::string>& toks, size_t& i,
    const std::function<bool(const std::string&)>& opens_a_checkpoint_section,
    const std::function<std::string(const std::vector<std::string>&, size_t&)>&
        consume_value_change,
    const std::function<std::string(const std::vector<std::string>&, size_t&,
                                    bool&)>& consume_other = nullptr) {
  while (i < toks.size()) {
    const std::string& t = toks[i];
    std::string err;
    if (opens_a_checkpoint_section(t)) {
      err = ConsumeCheckpointSection(toks, i, consume_value_change);
    } else if (t == "$comment") {
      err = ConsumeComment(toks, i);
    } else if (t[0] == '#') {
      err = ConsumeSimulationTime(toks, i);
    } else if (t[0] == '$') {
      bool handled = false;
      err = ConsumeOtherSimulationCommand(toks, i, consume_other, handled);
      if (!handled) {
        return "declaration command after simulation commands: " + t;
      }
    } else {
      err = consume_value_change(toks, i);
    }
    if (!err.empty()) return err;
  }
  return "";
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
