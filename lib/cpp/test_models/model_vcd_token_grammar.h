#pragma once

#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <string>
#include <vector>

inline bool IsPrintableAscii(const std::string& t) {
  if (t.empty()) return false;
  for (unsigned char c : t) {
    if (c < 33 || c > 126) return false;
  }
  return true;
}

inline bool IsDecimal(const std::string& t) {
  if (t.empty()) return false;
  for (char c : t) {
    if (c < '0' || c > '9') return false;
  }
  return true;
}

inline bool IsValueChar(char c) { return std::strchr("01xXzZ", c) != nullptr; }

inline bool IsFourStateDigits(const std::string& t) {
  if (t.empty()) return false;
  for (char c : t) {
    if (!IsValueChar(c)) return false;
  }
  return true;
}

inline bool IsScopeType(const std::string& t) {
  static const char* kinds[] = {"begin", "fork", "function", "module", "task"};
  for (const char* k : kinds) {
    if (t == k) return true;
  }
  return false;
}

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

inline bool IsTimescaleBody(const std::string& body) {
  static const char* nums[] = {"100", "10", "1"};
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

inline std::string ConsumeScalarValueChange(
    const std::vector<std::string>& toks, size_t& i) {
  const std::string& t = toks[i];
  if (t.size() < 2 || !IsPrintableAscii(t.substr(1))) {
    return "malformed scalar_value_change: " + t;
  }
  ++i;
  return "";
}

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

inline std::vector<std::string> CollectVarCodes(
    const std::vector<std::string>& toks) {
  std::vector<std::string> codes;
  for (size_t i = 0; i + 4 < toks.size(); ++i) {
    if (toks[i] == "$var") codes.push_back(toks[i + 3]);
  }
  return codes;
}

struct VcdDeclarationCommand {
  std::string keyword;
  std::vector<std::string> body;
};

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
    ++i;
    bool handled = false;
    std::string err = CheckFixedDeclarationBody(cmd, handled);
    if (!err.empty()) return err;
    if (handled) continue;
    err = check_body(cmd);
    if (!err.empty()) return err;
  }
  return "";
}

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

inline std::string ConsumeComment(const std::vector<std::string>& toks,
                                  size_t& i) {
  ++i;
  while (i < toks.size() && toks[i] != "$end") ++i;
  if (i >= toks.size()) return "$comment not terminated by $end";
  ++i;
  return "";
}

inline std::string ConsumeSimulationTime(const std::vector<std::string>& toks,
                                         size_t& i) {
  const std::string& t = toks[i];
  if (t.size() < 2 || !IsDecimal(t.substr(1))) {
    return "simulation_time is not # decimal_number: " + t;
  }
  ++i;
  return "";
}

inline std::string ConsumeOtherSimulationCommand(
    const std::vector<std::string>& toks, size_t& i,
    const std::function<std::string(const std::vector<std::string>&, size_t&,
                                    bool&)>& consume_other,
    bool& handled) {
  handled = false;
  if (!consume_other) return "";
  return consume_other(toks, i, handled);
}

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

inline bool NoFusedCommands(const std::vector<std::string>& toks) {
  for (const auto& t : toks) {
    if (t.find('$', 1) != std::string::npos) return false;
  }
  return true;
}
