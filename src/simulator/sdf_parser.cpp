#include "simulator/sdf_parser.h"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_specify.h"
#include "simulator/sdf_parser_internal.h"

namespace delta {

void SkipWhitespace(std::string_view& s) {
  while (!s.empty() && (std::isspace(s[0]) != 0)) s.remove_prefix(1);
}

static SdfToken MakeSingleChar(std::string_view& s, SdfTokKind kind) {
  SdfToken tok;
  tok.kind = kind;
  tok.text = s.substr(0, 1);
  s.remove_prefix(1);
  return tok;
}

static SdfToken LexString(std::string_view& s) {
  s.remove_prefix(1);
  size_t end = s.find('"');
  if (end == std::string_view::npos) end = s.size();
  SdfToken tok;
  tok.kind = SdfTokKind::kString;
  tok.text = s.substr(0, end);
  s.remove_prefix(std::min(end + 1, s.size()));
  return tok;
}

static size_t DigitRun(std::string_view s, size_t pos) {
  size_t len = 0;
  while (pos + len < s.size() && (std::isdigit(s[pos + len]) != 0)) ++len;
  return len;
}

static size_t NumberLength(std::string_view s, size_t first_digit,
                           bool& whole) {
  size_t len = first_digit + DigitRun(s, first_digit);
  if (len < s.size() && s[len] == '.') {
    len += 1 + DigitRun(s, len + 1);
    whole = false;
  }
  if (len >= s.size() || (s[len] != 'e' && s[len] != 'E')) return len;
  size_t exponent = len + 1;
  if (exponent < s.size() && (s[exponent] == '+' || s[exponent] == '-'))
    ++exponent;
  const size_t kDigits = DigitRun(s, exponent);
  if (kDigits == 0) return len;
  whole = false;
  return exponent + kDigits;
}

static SdfToken LexNumber(std::string_view& s) {
  const size_t kFirstDigit = (!s.empty() && s[0] == '-') ? 1 : 0;
  bool whole = true;
  const size_t kLen = NumberLength(s, kFirstDigit, whole);
  SdfToken tok;
  tok.kind = SdfTokKind::kNumber;
  tok.text = s.substr(0, kLen);
  tok.is_negative = kFirstDigit == 1;
  const std::string kMagnitude(s.substr(kFirstDigit, kLen - kFirstDigit));
  tok.real_val = std::strtod(kMagnitude.c_str(), nullptr);
  if (whole) {
    for (char digit : kMagnitude)
      tok.num_val = tok.num_val * 10 + (digit - '0');
  } else {
    tok.num_val = static_cast<uint64_t>(std::llround(tok.real_val));
  }
  s.remove_prefix(kLen);
  return tok;
}

static SdfToken LexIdent(std::string_view& s) {
  size_t len = 0;
  while (len < s.size() && s[len] != '(' && s[len] != ')' && s[len] != ':' &&
         s[len] != '"' && (std::isspace(s[len]) == 0)) {
    ++len;
  }
  SdfToken tok;
  tok.kind = SdfTokKind::kIdent;
  tok.text = s.substr(0, len);
  s.remove_prefix(len);
  return tok;
}

SdfToken NextSdfToken(std::string_view& s) {
  SkipWhitespace(s);
  if (s.empty()) return {SdfTokKind::kEof, {}, 0};
  char ch = s[0];
  if (ch == '(') return MakeSingleChar(s, SdfTokKind::kLParen);
  if (ch == ')') return MakeSingleChar(s, SdfTokKind::kRParen);
  if (ch == ':') return MakeSingleChar(s, SdfTokKind::kColon);
  if (ch == '"') return LexString(s);
  const bool kSignedNumber =
      ch == '-' && s.size() > 1 && (std::isdigit(s[1]) != 0);
  if ((std::isdigit(ch) != 0) || kSignedNumber) return LexNumber(s);
  return LexIdent(s);
}

bool Expect(std::string_view& s, SdfTokKind kind) {
  auto tok = NextSdfToken(s);
  return tok.kind == kind;
}

static void SetSdfTripleMember(SdfDelayValue& dv, int member,
                               const SdfToken& tok) {
  if (member == 0) {
    dv.min_val = tok.num_val;
    dv.min_real = tok.real_val;
    dv.min_negative = tok.is_negative;
  } else if (member == 1) {
    dv.typ_val = tok.num_val;
    dv.typ_real = tok.real_val;
    dv.typ_negative = tok.is_negative;
  } else {
    dv.max_val = tok.num_val;
    dv.max_real = tok.real_val;
    dv.max_negative = tok.is_negative;
  }
}

static bool ParseSdfValueBody(std::string_view& s, SdfDelayValue& dv) {
  bool written[3] = {false, false, false};
  bool triple = false;
  for (int member = 0; member < 3; ++member) {
    SkipWhitespace(s);
    if (!s.empty() && s[0] != ':' && s[0] != ')') {
      const SdfToken kTok = NextSdfToken(s);
      if (kTok.kind == SdfTokKind::kNumber) {
        SetSdfTripleMember(dv, member, kTok);
        written[member] = true;
      }
    }
    SkipWhitespace(s);
    if (member == 2 || s.empty() || s[0] != ':') break;
    Expect(s, SdfTokKind::kColon);
    triple = true;
  }
  if (!triple) {
    dv.typ_val = dv.max_val = dv.min_val;
    dv.typ_real = dv.max_real = dv.min_real;
    dv.typ_negative = dv.max_negative = dv.min_negative;
    written[1] = written[0];
    written[2] = written[0];
  }
  dv.min_empty = !written[0];
  dv.typ_empty = !written[1];
  dv.max_empty = !written[2];
  return written[0] || written[1] || written[2];
}

static std::string ParseSdfPort(std::string_view& s) {
  SkipWhitespace(s);

  if (!s.empty() && s[0] == '(') {
    return "";
  }
  auto tok = NextSdfToken(s);
  std::string port(tok.text);
  if (port.find('[') != std::string::npos &&
      port.find(']') == std::string::npos && !s.empty() && s[0] == ':') {
    size_t close = s.find(']');
    if (close != std::string_view::npos) {
      port += s.substr(0, close + 1);
      s.remove_prefix(close + 1);
    }
  }
  return port;
}

void SkipSdfParen(std::string_view& s) {
  int depth = 1;
  while (depth > 0 && !s.empty()) {
    auto tok = NextSdfToken(s);
    if (tok.kind == SdfTokKind::kLParen) ++depth;
    if (tok.kind == SdfTokKind::kRParen) --depth;
    if (tok.kind == SdfTokKind::kEof) break;
  }
}

std::vector<std::string> ParseSdfCondTokens(std::string_view& s) {
  std::vector<std::string> out;
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == '(' || s[0] == ')') break;
    auto tok = NextSdfToken(s);
    if (tok.kind == SdfTokKind::kEof) break;
    out.emplace_back(tok.text);
  }
  return out;
}

std::string JoinSdfCondTokens(const std::vector<std::string>& tokens,
                              std::size_t count) {
  std::string out;
  for (std::size_t i = 0; i < count && i < tokens.size(); ++i) {
    if (!out.empty()) out.push_back(' ');
    out.append(tokens[i]);
  }
  return out;
}

static std::string ParseSdfConditionText(std::string_view& s) {
  const auto kTokens = ParseSdfCondTokens(s);
  return JoinSdfCondTokens(kTokens, kTokens.size());
}

static SdfDelayValue ParseDelayValOrEmpty(std::string_view& s, bool* present) {
  SdfDelayValue dv;
  *present = false;
  if (!Expect(s, SdfTokKind::kLParen)) return dv;
  SkipWhitespace(s);
  if (!s.empty() && s[0] == ')') {
    Expect(s, SdfTokKind::kRParen);
    return dv;
  }
  *present = ParseSdfValueBody(s, dv);
  Expect(s, SdfTokKind::kRParen);
  return dv;
}

SdfDelayValue ParseDelayVal(std::string_view& s) {
  bool written = false;
  SdfDelayValue dv = ParseDelayValOrEmpty(s, &written);
  dv.empty = !written;
  return dv;
}

static SdfIopathDirection ParseExtendedDirection(std::string_view& s) {
  SdfIopathDirection d;
  if (!Expect(s, SdfTokKind::kLParen)) return d;
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    d.delay = ParseDelayValOrEmpty(s, &d.delay_present);
  }
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    d.reject = ParseDelayValOrEmpty(s, &d.reject_present);
  }
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    d.error = ParseDelayValOrEmpty(s, &d.error_present);
  }
  Expect(s, SdfTokKind::kRParen);
  return d;
}

static bool LooksLikeExtendedIopathDirection(std::string_view s) {
  if (s.empty() || s[0] != '(') return false;
  size_t i = 1;
  while (i < s.size() &&
         (std::isspace(static_cast<unsigned char>(s[i])) != 0)) {
    ++i;
  }
  return i < s.size() && s[i] == '(';
}

static void SkipOptionalIopathRetain(std::string_view& s) {
  SkipWhitespace(s);
  if (s.size() >= 7 && s[0] == '(') {
    auto save = s;
    Expect(s, SdfTokKind::kLParen);
    auto peek = NextSdfToken(s);
    if (peek.text == "RETAIN") {
      SkipSdfParen(s);
    } else {
      s = save;
    }
  }
}

static void ParseExtendedIopathDelays(std::string_view& s, SdfIopath& io) {
  while (io.directions.size() < 12) {
    SkipWhitespace(s);
    if (s.empty() || s[0] != '(') break;
    io.directions.push_back(ParseExtendedDirection(s));
    io.values.push_back(io.directions.back().delay);
  }
  if (!io.values.empty()) io.rise = io.values[0];
  if (io.values.size() > 1) io.fall = io.values[1];
  if (io.values.size() > 2) io.turnoff = io.values[2];
}

static void ParseSimpleIopathDelays(std::string_view& s, SdfIopath& io) {
  while (io.values.size() < 12) {
    SkipWhitespace(s);
    if (s.empty() || s[0] != '(') break;
    io.values.push_back(ParseDelayVal(s));
  }
  if (!io.values.empty()) io.rise = io.values[0];
  if (io.values.size() > 1) io.fall = io.values[1];
  if (io.values.size() > 2) io.turnoff = io.values[2];
}

static std::string ParseIopathSource(std::string_view& s, SdfIopath& io) {
  SkipWhitespace(s);
  if (s.empty() || s[0] != '(') return ParseSdfPort(s);
  Expect(s, SdfTokKind::kLParen);
  auto edge_tok = NextSdfToken(s);
  if (edge_tok.text == "posedge") {
    io.src_edge = SpecifyEdge::kPosedge;
  } else if (edge_tok.text == "negedge") {
    io.src_edge = SpecifyEdge::kNegedge;
  } else {
    io.src_edge_known = false;
  }
  std::string port = ParseSdfPort(s);
  Expect(s, SdfTokKind::kRParen);
  return port;
}

static SdfIopath ParseIopath(std::string_view& s) {
  SdfIopath io;
  io.src_port = ParseIopathSource(s, io);
  io.dst_port = ParseSdfPort(s);

  SkipOptionalIopathRetain(s);

  SkipWhitespace(s);
  io.extended_form = LooksLikeExtendedIopathDirection(s);
  if (io.extended_form) {
    ParseExtendedIopathDelays(s, io);
  } else {
    ParseSimpleIopathDelays(s, io);
  }
  Expect(s, SdfTokKind::kRParen);
  return io;
}

static void ParseInterconnectDelayList(std::string_view& s,
                                       SdfInterconnect& ic) {
  while (ic.values.size() < 12) {
    SkipWhitespace(s);
    if (s.empty() || s[0] != '(') break;
    if (LooksLikeExtendedIopathDirection(s)) {
      ic.directions.push_back(ParseExtendedDirection(s));
      ic.values.push_back(ic.directions.back().delay);
      ic.values.back().empty = !ic.directions.back().delay_present;
      continue;
    }
    SdfIopathDirection dir;
    dir.delay = ParseDelayVal(s);
    dir.delay_present = !dir.delay.empty;
    ic.directions.push_back(dir);
    ic.values.push_back(dir.delay);
  }
  if (!ic.values.empty()) ic.rise = ic.values[0];
  if (ic.values.size() > 1) ic.fall = ic.values[1];
}

static SdfInterconnect ParseInterconnectEntry(std::string_view& s) {
  SdfInterconnect ic;
  ic.kind = SdfInterconnectKind::kInterconnect;
  ic.src_port = ParseSdfPort(s);
  ic.dst_port = ParseSdfPort(s);
  ParseInterconnectDelayList(s, ic);
  Expect(s, SdfTokKind::kRParen);
  return ic;
}

static SdfInterconnect ParseLoadOnlyInterconnect(std::string_view& s,
                                                 SdfInterconnectKind kind) {
  SdfInterconnect ic;
  ic.kind = kind;
  ic.dst_port = ParseSdfPort(s);
  ParseInterconnectDelayList(s, ic);
  Expect(s, SdfTokKind::kRParen);
  return ic;
}

static SdfDevice ParseDeviceEntry(std::string_view& s) {
  SdfDevice dev;
  dev.port_instance = ParseSdfPort(s);
  while (dev.values.size() < 12) {
    SkipWhitespace(s);
    if (s.empty() || s[0] != '(') break;
    dev.values.push_back(ParseDelayVal(s));
  }
  if (!dev.values.empty()) dev.rise = dev.values[0];
  if (dev.values.size() > 1) dev.fall = dev.values[1];
  if (dev.values.size() > 2) dev.turnoff = dev.values[2];
  Expect(s, SdfTokKind::kRParen);
  return dev;
}

static SdfPulseLimit ParsePulseLimit(std::string_view& s) {
  SdfPulseLimit pl;
  pl.src_port = ParseSdfPort(s);
  pl.dst_port = ParseSdfPort(s);
  pl.reject = ParseDelayVal(s);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    pl.error = ParseDelayVal(s);
    pl.has_error = true;
  }
  Expect(s, SdfTokKind::kRParen);
  return pl;
}

static void RecordCellEntry(SdfCell& cell, SdfCellEntryKind kind,
                            size_t index) {
  SdfCellEntryRef ref;
  ref.kind = kind;
  ref.index = static_cast<uint32_t>(index);
  cell.entry_order.push_back(ref);
}

static void AddIopathToCell(SdfCell& cell, SdfFile& file, const SdfIopath& io) {
  if (!io.src_edge_known) {
    file.unannotatable.emplace_back("IOPATH");
    return;
  }
  cell.iopaths.push_back(io);
  RecordCellEntry(cell, SdfCellEntryKind::kIopath, cell.iopaths.size() - 1);
}

static void AddInterconnectToCell(SdfCell& cell, SdfInterconnect&& ic) {
  cell.interconnects.push_back(std::move(ic));
  RecordCellEntry(cell, SdfCellEntryKind::kInterconnect,
                  cell.interconnects.size() - 1);
}

static void ParseAndAddLoadOnlyInterconnect(std::string_view& s, SdfCell& cell,
                                            SdfInterconnectKind kind,
                                            bool increment) {
  auto ic = ParseLoadOnlyInterconnect(s, kind);
  ic.is_increment = increment;
  AddInterconnectToCell(cell, std::move(ic));
}

static void ParseCondDelayEntry(std::string_view& s, SdfCell& cell,
                                SdfFile& file, bool increment) {
  std::string cond = ParseSdfConditionText(s);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    Expect(s, SdfTokKind::kLParen);
    auto inner = NextSdfToken(s);
    if (inner.text == "IOPATH") {
      auto io = ParseIopath(s);
      io.is_increment = increment;
      io.condition = std::move(cond);
      AddIopathToCell(cell, file, io);
      Expect(s, SdfTokKind::kRParen);
      return;
    }

    SkipSdfParen(s);
  }
  file.unannotatable.emplace_back("COND");

  SkipWhitespace(s);
  if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
}

static void ParseCondElseDelayEntry(std::string_view& s, SdfCell& cell,
                                    SdfFile& file, bool increment) {
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    Expect(s, SdfTokKind::kLParen);
    auto inner = NextSdfToken(s);
    if (inner.text == "IOPATH") {
      auto io = ParseIopath(s);
      io.is_increment = increment;
      io.is_ifnone = true;
      AddIopathToCell(cell, file, io);
      Expect(s, SdfTokKind::kRParen);
      return;
    }
    SkipSdfParen(s);
  }
  file.unannotatable.emplace_back("CONDELSE");
  SkipWhitespace(s);
  if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
}

static void ParsePulseLimitDelayEntry(std::string_view& s, SdfCell& cell,
                                      bool is_percent, bool increment) {
  auto pl = ParsePulseLimit(s);
  pl.is_percent = is_percent;
  pl.is_increment = increment;
  cell.pulse_limits.push_back(pl);
  RecordCellEntry(cell, SdfCellEntryKind::kPulseLimit,
                  cell.pulse_limits.size() - 1);
}

static void ParseInterconnectDelayEntry(std::string_view& s, SdfCell& cell,
                                        bool increment) {
  auto ic = ParseInterconnectEntry(s);
  ic.is_increment = increment;
  AddInterconnectToCell(cell, std::move(ic));
}

static void ParseDeviceDelayEntry(std::string_view& s, SdfCell& cell,
                                  bool increment) {
  auto dev = ParseDeviceEntry(s);
  dev.is_increment = increment;
  cell.devices.push_back(std::move(dev));
  RecordCellEntry(cell, SdfCellEntryKind::kDevice, cell.devices.size() - 1);
}

static void ParseIopathDelayEntry(std::string_view& s, SdfCell& cell,
                                  SdfFile& file, bool increment) {
  auto io = ParseIopath(s);
  io.is_increment = increment;
  AddIopathToCell(cell, file, io);
}

static void HandleDelayEntry(std::string_view& s, SdfCell& cell, SdfFile& file,
                             const SdfToken& kw, bool increment) {
  if (kw.text == "PATHPULSE" || kw.text == "PATHPULSEPERCENT") {
    ParsePulseLimitDelayEntry(s, cell, kw.text == "PATHPULSEPERCENT",
                              increment);
  } else if (kw.text == "INTERCONNECT") {
    ParseInterconnectDelayEntry(s, cell, increment);
  } else if (kw.text == "PORT") {
    ParseAndAddLoadOnlyInterconnect(s, cell, SdfInterconnectKind::kPort,
                                    increment);
  } else if (kw.text == "NETDELAY") {
    ParseAndAddLoadOnlyInterconnect(s, cell, SdfInterconnectKind::kNetdelay,
                                    increment);
  } else if (kw.text == "IOPATH") {
    ParseIopathDelayEntry(s, cell, file, increment);
  } else if (kw.text == "DEVICE") {
    ParseDeviceDelayEntry(s, cell, increment);
  } else if (kw.text == "COND") {
    ParseCondDelayEntry(s, cell, file, increment);
  } else if (kw.text == "CONDELSE") {
    ParseCondElseDelayEntry(s, cell, file, increment);
  } else {
    file.unannotatable.emplace_back(kw.text);
    SkipSdfParen(s);
  }
}

static void ParseDelaySection(std::string_view& s, SdfCell& cell, SdfFile& file,
                              bool increment) {
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == ')') break;
    Expect(s, SdfTokKind::kLParen);
    auto kw = NextSdfToken(s);
    HandleDelayEntry(s, cell, file, kw, increment);
  }
  Expect(s, SdfTokKind::kRParen);
}

static void ParseDelaySpec(std::string_view& s, SdfCell& cell, SdfFile& file) {
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] != '(') break;
    Expect(s, SdfTokKind::kLParen);
    auto mode = NextSdfToken(s);
    if (mode.text != "ABSOLUTE" && mode.text != "INCREMENT") {
      file.unannotatable.emplace_back(mode.text);
      SkipSdfParen(s);
      continue;
    }
    ParseDelaySection(s, cell, file, mode.text == "INCREMENT");
  }
  Expect(s, SdfTokKind::kRParen);
}

static void ParseTimingCheckSection(std::string_view& s, SdfCell& cell,
                                    SdfFile& file) {
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == ')') break;
    Expect(s, SdfTokKind::kLParen);
    auto kw = NextSdfToken(s);
    SdfCheckType ct = SdfCheckType::kSetup;
    if (!MapCheckType(kw.text, ct)) {
      file.unannotatable.emplace_back(kw.text);
      SkipSdfParen(s);
      continue;
    }
    auto tc = ParseOneTc(s, ct);
    cell.timing_checks.push_back(tc);
    RecordCellEntry(cell, SdfCellEntryKind::kTimingCheck,
                    cell.timing_checks.size() - 1);
  }
  Expect(s, SdfTokKind::kRParen);
}

static SdfDelayValue ParseLabelValue(std::string_view& s) {
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') return ParseDelayVal(s);
  SdfDelayValue dv;
  auto num = NextSdfToken(s);
  if (num.kind == SdfTokKind::kNumber) {
    dv.min_val = num.num_val;
    dv.typ_val = num.num_val;
    dv.max_val = num.num_val;
    dv.min_real = dv.typ_real = dv.max_real = num.real_val;
  }
  return dv;
}

static void ParseLabelType(std::string_view& s, SdfCell& cell, SdfFile& file) {
  auto mode = NextSdfToken(s);
  if (mode.text != "ABSOLUTE" && mode.text != "INCREMENT") {
    file.unannotatable.emplace_back("LABEL");
    SkipSdfParen(s);
    return;
  }
  const bool kIncrement = (mode.text == "INCREMENT");
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == ')') break;
    Expect(s, SdfTokKind::kLParen);
    auto name_tok = NextSdfToken(s);
    SdfSpecparam sp;
    sp.name = std::string(name_tok.text);
    sp.value = ParseLabelValue(s);
    sp.is_increment = kIncrement;
    Expect(s, SdfTokKind::kRParen);

    cell.specparams.push_back(std::move(sp));
    RecordCellEntry(cell, SdfCellEntryKind::kSpecparam,
                    cell.specparams.size() - 1);
  }
  Expect(s, SdfTokKind::kRParen);
}

static void ParseLabelSection(std::string_view& s, SdfCell& cell,
                              SdfFile& file) {
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] != '(') break;
    Expect(s, SdfTokKind::kLParen);
    ParseLabelType(s, cell, file);
  }
  Expect(s, SdfTokKind::kRParen);
}

static SdfCell ParseCell(std::string_view& s, SdfFile& file) {
  SdfCell cell;
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == ')') break;
    Expect(s, SdfTokKind::kLParen);
    auto kw = NextSdfToken(s);
    if (kw.text == "CELLTYPE") {
      auto val = NextSdfToken(s);
      cell.cell_type = std::string(val.text);
      Expect(s, SdfTokKind::kRParen);
    } else if (kw.text == "INSTANCE") {
      SkipWhitespace(s);
      if (!s.empty() && s[0] != ')')
        cell.instance = std::string(NextSdfToken(s).text);
      Expect(s, SdfTokKind::kRParen);
    } else if (kw.text == "DELAY") {
      ParseDelaySpec(s, cell, file);
    } else if (kw.text == "TIMINGCHECK") {
      ParseTimingCheckSection(s, cell, file);
    } else if (kw.text == "LABEL") {
      ParseLabelSection(s, cell, file);
    } else {
      SkipSdfParen(s);
    }
  }
  Expect(s, SdfTokKind::kRParen);
  return cell;
}

static double ParseSdfTimescale(std::string_view& s) {
  const SdfToken kNumber = NextSdfToken(s);
  SkipWhitespace(s);
  std::string_view unit;
  if (!s.empty() && s[0] != ')') unit = NextSdfToken(s).text;
  Expect(s, SdfTokKind::kRParen);
  static constexpr std::pair<std::string_view, double> kUnits[] = {
      {"s", 1.0},   {"ms", 1e-3},  {"us", 1e-6},
      {"ns", 1e-9}, {"ps", 1e-12}, {"fs", 1e-15}};
  for (const auto& [name, seconds] : kUnits) {
    if (unit == name) return kNumber.real_val * seconds;
  }
  return 0.0;
}

bool ParseSdf(std::string_view input, SdfFile& out) {
  if (!Expect(input, SdfTokKind::kLParen)) return false;
  auto delayfile = NextSdfToken(input);
  if (delayfile.text != "DELAYFILE") return false;

  while (true) {
    SkipWhitespace(input);
    if (input.empty() || input[0] == ')') break;
    Expect(input, SdfTokKind::kLParen);
    auto kw = NextSdfToken(input);
    if (kw.text == "SDFVERSION") {
      auto ver = NextSdfToken(input);
      out.version = std::string(ver.text);
      Expect(input, SdfTokKind::kRParen);
    } else if (kw.text == "DESIGN") {
      auto design = NextSdfToken(input);
      out.design = std::string(design.text);
      Expect(input, SdfTokKind::kRParen);
    } else if (kw.text == "TIMESCALE") {
      out.timescale_seconds = ParseSdfTimescale(input);
    } else if (kw.text == "CELL") {
      out.cells.push_back(ParseCell(input, out));
    } else {
      SkipSdfParen(input);
    }
  }
  return true;
}

}  // namespace delta
