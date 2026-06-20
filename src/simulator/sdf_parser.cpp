

#include "simulator/sdf_parser.h"

#include <algorithm>
#include <array>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <fstream>
#include <initializer_list>
#include <string>

#include "simulator/specify.h"

namespace delta {

enum class SdfTokKind : uint8_t {
  kLParen,
  kRParen,
  kColon,
  kIdent,
  kString,
  kNumber,
  kEof,
};

struct SdfToken {
  SdfTokKind kind = SdfTokKind::kEof;
  std::string_view text;
  uint64_t num_val = 0;
};

static void SkipWhitespace(std::string_view& s) {
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

static SdfToken LexNumber(std::string_view& s) {
  size_t len = 0;
  while (len < s.size() && (std::isdigit(s[len]) != 0)) ++len;
  SdfToken tok;
  tok.kind = SdfTokKind::kNumber;
  tok.text = s.substr(0, len);
  tok.num_val = 0;
  for (size_t i = 0; i < len; ++i) {
    tok.num_val = tok.num_val * 10 + (s[i] - '0');
  }
  s.remove_prefix(len);
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

static SdfToken NextSdfToken(std::string_view& s) {
  SkipWhitespace(s);
  if (s.empty()) return {SdfTokKind::kEof, {}, 0};
  char ch = s[0];
  if (ch == '(') return MakeSingleChar(s, SdfTokKind::kLParen);
  if (ch == ')') return MakeSingleChar(s, SdfTokKind::kRParen);
  if (ch == ':') return MakeSingleChar(s, SdfTokKind::kColon);
  if (ch == '"') return LexString(s);
  if (std::isdigit(ch) != 0) return LexNumber(s);
  return LexIdent(s);
}

static bool Expect(std::string_view& s, SdfTokKind kind) {
  auto tok = NextSdfToken(s);
  return tok.kind == kind;
}

static SdfDelayValue ParseDelayVal(std::string_view& s) {
  SdfDelayValue dv;

  if (!Expect(s, SdfTokKind::kLParen)) return dv;
  auto first = NextSdfToken(s);
  if (first.kind == SdfTokKind::kNumber) {
    dv.min_val = first.num_val;
    dv.typ_val = first.num_val;
    dv.max_val = first.num_val;

    SkipWhitespace(s);
    if (!s.empty() && s[0] == ':') {
      Expect(s, SdfTokKind::kColon);
      auto typ = NextSdfToken(s);
      if (typ.kind == SdfTokKind::kNumber) dv.typ_val = typ.num_val;
      Expect(s, SdfTokKind::kColon);
      auto max_tok = NextSdfToken(s);
      if (max_tok.kind == SdfTokKind::kNumber) dv.max_val = max_tok.num_val;
    }
  }
  Expect(s, SdfTokKind::kRParen);
  return dv;
}

static std::string ParseSdfPort(std::string_view& s) {
  SkipWhitespace(s);

  if (!s.empty() && s[0] == '(') {
    return "";
  }
  auto tok = NextSdfToken(s);
  return std::string(tok.text);
}

static void SkipSdfParen(std::string_view& s) {
  int depth = 1;
  while (depth > 0 && !s.empty()) {
    auto tok = NextSdfToken(s);
    if (tok.kind == SdfTokKind::kLParen) ++depth;
    if (tok.kind == SdfTokKind::kRParen) --depth;
    if (tok.kind == SdfTokKind::kEof) break;
  }
}

static std::string ParseSdfConditionText(std::string_view& s) {
  std::string out;
  while (true) {
    SkipWhitespace(s);
    if (s.empty()) break;
    if (s[0] == '(') break;
    auto tok = NextSdfToken(s);
    if (tok.kind == SdfTokKind::kEof) break;
    if (tok.kind == SdfTokKind::kRParen) break;
    if (!out.empty()) out.push_back(' ');
    out.append(tok.text);
  }
  return out;
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
  auto first = NextSdfToken(s);
  if (first.kind == SdfTokKind::kNumber) {
    dv.min_val = first.num_val;
    dv.typ_val = first.num_val;
    dv.max_val = first.num_val;
    *present = true;
    SkipWhitespace(s);
    if (!s.empty() && s[0] == ':') {
      Expect(s, SdfTokKind::kColon);
      auto typ = NextSdfToken(s);
      if (typ.kind == SdfTokKind::kNumber) dv.typ_val = typ.num_val;
      Expect(s, SdfTokKind::kColon);
      auto max_tok = NextSdfToken(s);
      if (max_tok.kind == SdfTokKind::kNumber) dv.max_val = max_tok.num_val;
    }
  }
  Expect(s, SdfTokKind::kRParen);
  return dv;
}

struct ExtendedIopathDir {
  SdfDelayValue delay;
  bool delay_present = false;
  SdfDelayValue reject;
  bool reject_present = false;
  SdfDelayValue error;
  bool error_present = false;
};

static ExtendedIopathDir ParseExtendedDirection(std::string_view& s) {
  ExtendedIopathDir d;
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

static SdfIopath ParseIopath(std::string_view& s) {
  SdfIopath io;
  io.src_port = ParseSdfPort(s);
  io.dst_port = ParseSdfPort(s);

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

  SkipWhitespace(s);
  io.extended_form = LooksLikeExtendedIopathDirection(s);
  if (io.extended_form) {
    auto rise_dir = ParseExtendedDirection(s);
    if (rise_dir.delay_present) io.rise = rise_dir.delay;
    io.rise_delay_present = rise_dir.delay_present;
    io.rise_reject = rise_dir.reject;
    io.rise_reject_present = rise_dir.reject_present;
    io.rise_error = rise_dir.error;
    io.rise_error_present = rise_dir.error_present;
    SkipWhitespace(s);
    if (!s.empty() && s[0] == '(') {
      auto fall_dir = ParseExtendedDirection(s);
      if (fall_dir.delay_present) io.fall = fall_dir.delay;
      io.fall_delay_present = fall_dir.delay_present;
      io.fall_reject = fall_dir.reject;
      io.fall_reject_present = fall_dir.reject_present;
      io.fall_error = fall_dir.error;
      io.fall_error_present = fall_dir.error_present;
    }
    SkipWhitespace(s);
    if (!s.empty() && s[0] == '(') {
      auto turnoff_dir = ParseExtendedDirection(s);

      if (turnoff_dir.delay_present) io.turnoff = turnoff_dir.delay;
    }
  } else {
    io.rise = ParseDelayVal(s);
    SkipWhitespace(s);
    if (!s.empty() && s[0] == '(') {
      io.fall = ParseDelayVal(s);
    }
    SkipWhitespace(s);
    if (!s.empty() && s[0] == '(') {
      io.turnoff = ParseDelayVal(s);
    }
  }
  Expect(s, SdfTokKind::kRParen);
  return io;
}

static SdfCheckType MapCheckType(std::string_view name) {
  if (name == "SETUP") return SdfCheckType::kSetup;
  if (name == "HOLD") return SdfCheckType::kHold;
  if (name == "SETUPHOLD") return SdfCheckType::kSetuphold;
  if (name == "RECOVERY") return SdfCheckType::kRecovery;
  if (name == "REMOVAL") return SdfCheckType::kRemoval;
  if (name == "RECREM") return SdfCheckType::kRecrem;
  if (name == "WIDTH") return SdfCheckType::kWidth;
  if (name == "PERIOD") return SdfCheckType::kPeriod;
  if (name == "SKEW") return SdfCheckType::kSkew;

  if (name == "BIDIRECTSKEW") return SdfCheckType::kBidirectskew;
  if (name == "NOCHANGE") return SdfCheckType::kNochange;
  return SdfCheckType::kSetup;
}

struct SdfSignalRef {
  std::string port;
  SpecifyEdge edge = SpecifyEdge::kNone;

  std::string condition;
};

static SdfSignalRef ParseSdfSignal(std::string_view& s) {
  SdfSignalRef ref;
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    Expect(s, SdfTokKind::kLParen);
    auto first_tok = NextSdfToken(s);

    if (first_tok.text == "COND") {
      ref.condition = ParseSdfConditionText(s);
      SkipWhitespace(s);
      if (!s.empty() && s[0] == '(') {
        Expect(s, SdfTokKind::kLParen);
        auto edge_tok = NextSdfToken(s);
        if (edge_tok.text == "posedge")
          ref.edge = SpecifyEdge::kPosedge;
        else if (edge_tok.text == "negedge")
          ref.edge = SpecifyEdge::kNegedge;
        auto port_tok = NextSdfToken(s);
        ref.port = std::string(port_tok.text);
        Expect(s, SdfTokKind::kRParen);
      } else {
        auto port_tok = NextSdfToken(s);
        ref.port = std::string(port_tok.text);
      }
      Expect(s, SdfTokKind::kRParen);
      return ref;
    }
    if (first_tok.text == "posedge") ref.edge = SpecifyEdge::kPosedge;
    if (first_tok.text == "negedge") ref.edge = SpecifyEdge::kNegedge;
    auto port_tok = NextSdfToken(s);
    ref.port = std::string(port_tok.text);
    Expect(s, SdfTokKind::kRParen);
  } else {
    auto tok = NextSdfToken(s);
    ref.port = std::string(tok.text);
  }
  return ref;
}

static SdfTimingCheck ParseOneTc(std::string_view& s, SdfCheckType type) {
  SdfTimingCheck tc;
  tc.check_type = type;

  const bool single_signal =
      (type == SdfCheckType::kWidth || type == SdfCheckType::kPeriod);
  auto first = ParseSdfSignal(s);
  if (single_signal) {
    tc.ref_port = first.port;
    tc.ref_edge = first.edge;

    tc.condition = std::move(first.condition);
  } else {
    tc.data_port = first.port;
    tc.data_edge = first.edge;
    auto ref = ParseSdfSignal(s);
    tc.ref_port = ref.port;
    tc.ref_edge = ref.edge;

    tc.condition = std::move(ref.condition);
  }
  tc.limit = ParseDelayVal(s);

  const bool two_value =
      (type == SdfCheckType::kSetuphold || type == SdfCheckType::kRecrem ||
       type == SdfCheckType::kBidirectskew || type == SdfCheckType::kNochange);
  if (two_value) {
    SkipWhitespace(s);
    if (!s.empty() && s[0] == '(') {
      tc.limit2 = ParseDelayVal(s);
    }
  }
  Expect(s, SdfTokKind::kRParen);
  return tc;
}

static SdfInterconnect ParseInterconnectEntry(std::string_view& s) {
  SdfInterconnect ic;
  ic.kind = SdfInterconnectKind::kInterconnect;
  ic.src_port = ParseSdfPort(s);
  ic.dst_port = ParseSdfPort(s);
  ic.rise = ParseDelayVal(s);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    ic.fall = ParseDelayVal(s);
  }
  Expect(s, SdfTokKind::kRParen);
  return ic;
}

static SdfInterconnect ParseLoadOnlyInterconnect(std::string_view& s,
                                                 SdfInterconnectKind kind) {
  SdfInterconnect ic;
  ic.kind = kind;
  ic.dst_port = ParseSdfPort(s);
  ic.rise = ParseDelayVal(s);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    ic.fall = ParseDelayVal(s);
  }
  Expect(s, SdfTokKind::kRParen);
  return ic;
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

static void RecordDelayEntry(SdfCell& cell, SdfDelayEntryKind kind,
                             size_t index) {
  SdfDelayEntryRef ref;
  ref.kind = kind;
  ref.index = static_cast<uint32_t>(index);
  cell.delay_entry_order.push_back(ref);
}

static void ParseDelaySection(std::string_view& s, SdfCell& cell, SdfFile& file,
                              bool increment) {
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == ')') break;
    Expect(s, SdfTokKind::kLParen);
    auto kw = NextSdfToken(s);
    if (kw.text == "PATHPULSE" || kw.text == "PATHPULSEPERCENT") {
      auto pl = ParsePulseLimit(s);
      pl.is_percent = (kw.text == "PATHPULSEPERCENT");
      cell.pulse_limits.push_back(pl);
      RecordDelayEntry(cell, SdfDelayEntryKind::kPulseLimit,
                       cell.pulse_limits.size() - 1);
      continue;
    }

    if (kw.text == "INTERCONNECT") {
      auto ic = ParseInterconnectEntry(s);
      ic.is_increment = increment;
      cell.interconnects.push_back(std::move(ic));
      RecordDelayEntry(cell, SdfDelayEntryKind::kInterconnect,
                       cell.interconnects.size() - 1);
      continue;
    }
    if (kw.text == "PORT") {
      auto ic = ParseLoadOnlyInterconnect(s, SdfInterconnectKind::kPort);
      ic.is_increment = increment;
      cell.interconnects.push_back(std::move(ic));
      RecordDelayEntry(cell, SdfDelayEntryKind::kInterconnect,
                       cell.interconnects.size() - 1);
      continue;
    }
    if (kw.text == "NETDELAY") {
      auto ic = ParseLoadOnlyInterconnect(s, SdfInterconnectKind::kNetdelay);
      ic.is_increment = increment;
      cell.interconnects.push_back(std::move(ic));
      RecordDelayEntry(cell, SdfDelayEntryKind::kInterconnect,
                       cell.interconnects.size() - 1);
      continue;
    }
    if (kw.text == "IOPATH") {
      auto io = ParseIopath(s);
      io.is_increment = increment;
      cell.iopaths.push_back(io);
      RecordDelayEntry(cell, SdfDelayEntryKind::kIopath,
                       cell.iopaths.size() - 1);
    } else if (kw.text == "COND") {
      std::string cond = ParseSdfConditionText(s);
      SkipWhitespace(s);
      if (!s.empty() && s[0] == '(') {
        Expect(s, SdfTokKind::kLParen);
        auto inner = NextSdfToken(s);
        if (inner.text == "IOPATH") {
          auto io = ParseIopath(s);
          io.is_increment = increment;
          io.condition = std::move(cond);
          cell.iopaths.push_back(io);
          RecordDelayEntry(cell, SdfDelayEntryKind::kIopath,
                           cell.iopaths.size() - 1);
          Expect(s, SdfTokKind::kRParen);
          continue;
        }

        SkipSdfParen(s);
      }
      file.unannotatable.emplace_back("COND");

      SkipWhitespace(s);
      if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
    } else if (kw.text == "CONDELSE") {
      SkipWhitespace(s);
      if (!s.empty() && s[0] == '(') {
        Expect(s, SdfTokKind::kLParen);
        auto inner = NextSdfToken(s);
        if (inner.text == "IOPATH") {
          auto io = ParseIopath(s);
          io.is_increment = increment;
          io.is_ifnone = true;
          cell.iopaths.push_back(io);
          RecordDelayEntry(cell, SdfDelayEntryKind::kIopath,
                           cell.iopaths.size() - 1);
          Expect(s, SdfTokKind::kRParen);
          continue;
        }
        SkipSdfParen(s);
      }
      file.unannotatable.emplace_back("CONDELSE");
      SkipWhitespace(s);
      if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
    } else {
      file.unannotatable.emplace_back(kw.text);
      SkipSdfParen(s);
    }
  }
  Expect(s, SdfTokKind::kRParen);
}

static void ParseTimingCheckSection(std::string_view& s, SdfCell& cell) {
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == ')') break;
    Expect(s, SdfTokKind::kLParen);
    auto kw = NextSdfToken(s);
    SdfCheckType ct = MapCheckType(kw.text);
    auto tc = ParseOneTc(s, ct);
    cell.timing_checks.push_back(tc);
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
  }
  return dv;
}

static void ParseLabelSection(std::string_view& s, SdfCell& cell,
                              SdfFile& file) {
  SkipWhitespace(s);
  if (s.empty() || s[0] != '(') {
    Expect(s, SdfTokKind::kRParen);
    return;
  }
  Expect(s, SdfTokKind::kLParen);
  auto mode = NextSdfToken(s);

  if (mode.text != "ABSOLUTE" && mode.text != "INCREMENT") {
    file.unannotatable.emplace_back("LABEL");
    SkipSdfParen(s);
    SkipWhitespace(s);
    if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
    return;
  }
  const bool increment = (mode.text == "INCREMENT");
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == ')') break;
    Expect(s, SdfTokKind::kLParen);
    auto name_tok = NextSdfToken(s);
    SdfSpecparam sp;
    sp.name = std::string(name_tok.text);
    sp.value = ParseLabelValue(s);
    sp.is_increment = increment;
    Expect(s, SdfTokKind::kRParen);

    cell.specparams.push_back(std::move(sp));
  }
  Expect(s, SdfTokKind::kRParen);
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
      auto val = NextSdfToken(s);
      cell.instance = std::string(val.text);
      Expect(s, SdfTokKind::kRParen);
    } else if (kw.text == "DELAY") {
      Expect(s, SdfTokKind::kLParen);
      auto mode = NextSdfToken(s);
      bool inc = (mode.text == "INCREMENT");
      ParseDelaySection(s, cell, file, inc);
      Expect(s, SdfTokKind::kRParen);
    } else if (kw.text == "TIMINGCHECK") {
      ParseTimingCheckSection(s, cell);
    } else if (kw.text == "LABEL") {
      ParseLabelSection(s, cell, file);
    } else {
      SkipSdfParen(s);
    }
  }
  Expect(s, SdfTokKind::kRParen);
  return cell;
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
    } else if (kw.text == "CELL") {
      out.cells.push_back(ParseCell(input, out));
    } else {
      SkipSdfParen(input);
    }
  }
  return true;
}

static uint64_t SelectMtm(const SdfDelayValue& dv, SdfMtm mtm) {
  switch (mtm) {
    case SdfMtm::kMinimum:
      return dv.min_val;
    case SdfMtm::kTypical:
      return dv.typ_val;
    case SdfMtm::kMaximum:
      return dv.max_val;
  }
  return dv.typ_val;
}

std::vector<uint64_t> ExpandSdfDelays(const std::vector<SdfDelayValue>& vals,
                                      SdfMtm mtm) {
  std::vector<uint64_t> out(12, 0);
  if (vals.empty()) return out;

  const std::size_t n = vals.size();
  const uint64_t v1 = SelectMtm(vals[0], mtm);

  if (n != 1 && n != 2 && n != 3 && n != 6 && n != 12) {
    std::fill(out.begin(), out.end(), v1);
    return out;
  }

  if (n == 1) {
    std::fill(out.begin(), out.end(), v1);
    return out;
  }

  const uint64_t v2 = SelectMtm(vals[1], mtm);
  if (n == 2) {
    out[0] = v1;
    out[1] = v2;
    out[2] = v1;
    out[3] = v1;
    out[4] = v2;
    out[5] = v2;
    out[6] = v1;
    out[7] = v1;
    out[8] = v2;
    out[9] = v2;
    out[10] = std::max(v1, v2);
    out[11] = std::min(v1, v2);
    return out;
  }

  const uint64_t v3 = SelectMtm(vals[2], mtm);
  if (n == 3) {
    out[0] = v1;
    out[1] = v2;
    out[2] = v3;
    out[3] = v1;
    out[4] = v3;
    out[5] = v2;
    out[6] = std::min(v1, v3);
    out[7] = std::max(v1, v3);
    out[8] = std::min(v2, v3);
    out[9] = v2;
    out[10] = v3;
    out[11] = std::min(v1, v2);
    return out;
  }

  const uint64_t v4 = SelectMtm(vals[3], mtm);
  const uint64_t v5 = SelectMtm(vals[4], mtm);
  const uint64_t v6 = SelectMtm(vals[5], mtm);
  if (n == 6) {
    out[0] = v1;
    out[1] = v2;
    out[2] = v3;
    out[3] = v4;
    out[4] = v5;
    out[5] = v6;
    out[6] = std::min(v1, v3);
    out[7] = std::max(v1, v4);
    out[8] = std::min(v2, v5);
    out[9] = std::max(v2, v6);
    out[10] = std::max(v3, v5);
    out[11] = std::min(v4, v6);
    return out;
  }

  for (std::size_t i = 0; i < 12; ++i) {
    out[i] = SelectMtm(vals[i], mtm);
  }
  return out;
}

std::array<uint64_t, 4> ReduceSdfDelaysToThree(
    const std::vector<SdfDelayValue>& vals, SdfMtm mtm) {
  std::array<uint64_t, 4> out{0, 0, 0, 0};
  if (vals.empty()) return out;

  out[0] = SelectMtm(vals[0], mtm);
  out[1] = vals.size() >= 2 ? SelectMtm(vals[1], mtm) : out[0];
  out[2] = vals.size() >= 3 ? SelectMtm(vals[2], mtm) : out[0];

  out[3] = std::min({out[0], out[1], out[2]});
  return out;
}

static std::vector<SdfTcAnnotation> ExpandSdfTimingCheckTargets(
    const SdfTimingCheck& tc, SdfMtm mtm) {
  const uint64_t v1 = SelectMtm(tc.limit, mtm);
  const uint64_t v2 = SelectMtm(tc.limit2, mtm);
  std::vector<SdfTcAnnotation> targets;
  auto push = [&](TimingCheckKind kind) -> SdfTcAnnotation& {
    SdfTcAnnotation a;
    a.kind = kind;
    a.ref_signal = tc.ref_port;
    a.ref_edge = tc.ref_edge;
    a.data_signal = tc.data_port;
    a.data_edge = tc.data_edge;
    a.condition = tc.condition;
    targets.push_back(std::move(a));
    return targets.back();
  };
  switch (tc.check_type) {
    case SdfCheckType::kSetup: {
      auto& s = push(TimingCheckKind::kSetup);
      s.set_limit = true;
      s.limit = v1;
      auto& sh = push(TimingCheckKind::kSetuphold);
      sh.set_limit = true;
      sh.limit = v1;
      break;
    }
    case SdfCheckType::kHold: {
      auto& h = push(TimingCheckKind::kHold);
      h.set_limit = true;
      h.limit = v1;
      auto& sh = push(TimingCheckKind::kSetuphold);
      sh.set_limit2 = true;
      sh.limit2 = v1;
      break;
    }
    case SdfCheckType::kSetuphold: {
      auto& s = push(TimingCheckKind::kSetup);
      s.set_limit = true;
      s.limit = v1;
      auto& h = push(TimingCheckKind::kHold);
      h.set_limit = true;
      h.limit = v2;
      auto& sh = push(TimingCheckKind::kSetuphold);
      sh.set_limit = true;
      sh.limit = v1;
      sh.set_limit2 = true;
      sh.limit2 = v2;
      break;
    }
    case SdfCheckType::kRecovery: {
      auto& r = push(TimingCheckKind::kRecovery);
      r.set_limit = true;
      r.limit = v1;
      auto& rr = push(TimingCheckKind::kRecrem);
      rr.set_limit = true;
      rr.limit = v1;
      break;
    }
    case SdfCheckType::kRemoval: {
      auto& r = push(TimingCheckKind::kRemoval);
      r.set_limit = true;
      r.limit = v1;
      auto& rr = push(TimingCheckKind::kRecrem);
      rr.set_limit2 = true;
      rr.limit2 = v1;
      break;
    }
    case SdfCheckType::kRecrem: {
      auto& r = push(TimingCheckKind::kRecovery);
      r.set_limit = true;
      r.limit = v1;
      auto& rm = push(TimingCheckKind::kRemoval);
      rm.set_limit = true;
      rm.limit = v2;
      auto& rr = push(TimingCheckKind::kRecrem);
      rr.set_limit = true;
      rr.limit = v1;
      rr.set_limit2 = true;
      rr.limit2 = v2;
      break;
    }
    case SdfCheckType::kSkew: {
      auto& s = push(TimingCheckKind::kSkew);
      s.set_limit = true;
      s.limit = v1;
      auto& ts = push(TimingCheckKind::kTimeskew);
      ts.set_limit = true;
      ts.limit = v1;
      break;
    }
    case SdfCheckType::kBidirectskew: {
      auto& fs = push(TimingCheckKind::kFullskew);
      fs.set_limit = true;
      fs.limit = v1;
      fs.set_limit2 = true;
      fs.limit2 = v2;
      break;
    }
    case SdfCheckType::kWidth: {
      auto& w = push(TimingCheckKind::kWidth);
      w.set_limit = true;
      w.limit = v1;
      break;
    }
    case SdfCheckType::kPeriod: {
      auto& p = push(TimingCheckKind::kPeriod);
      p.set_limit = true;
      p.limit = v1;
      break;
    }
    case SdfCheckType::kNochange: {
      auto& nc = push(TimingCheckKind::kNochange);
      nc.set_start_edge_offset = true;
      nc.start_edge_offset = static_cast<int64_t>(v1);
      nc.set_end_edge_offset = true;
      nc.end_edge_offset = static_cast<int64_t>(v2);
      break;
    }
  }
  return targets;
}

static bool CellInScope(std::string_view instance, std::string_view scope) {
  if (scope.empty()) return true;
  if (instance.size() < scope.size()) return false;
  if (instance.compare(0, scope.size(), scope) != 0) return false;
  if (instance.size() == scope.size()) return true;
  const char sep = instance[scope.size()];
  return sep == '/' || sep == '.';
}

SdfAnnotationResult AnnotateSdfToManager(const SdfFile& file,
                                         SpecifyManager& mgr, SdfMtm mtm,
                                         std::string_view scope) {
  SdfAnnotationResult result;

  for (const auto& kw : file.unannotatable) {
    result.warnings.push_back("SDF annotator: unable to annotate " + kw +
                              " construct");
  }

  for (const auto& cell : file.cells) {
    if (!CellInScope(cell.instance, scope)) continue;
    std::vector<SdfDelayEntryRef> derived;
    const std::vector<SdfDelayEntryRef>* order = &cell.delay_entry_order;
    if (order->empty() &&
        (!cell.iopaths.empty() || !cell.pulse_limits.empty() ||
         !cell.interconnects.empty())) {
      derived.reserve(cell.iopaths.size() + cell.pulse_limits.size() +
                      cell.interconnects.size());
      for (uint32_t i = 0; i < cell.iopaths.size(); ++i) {
        derived.push_back({SdfDelayEntryKind::kIopath, i});
      }
      for (uint32_t i = 0; i < cell.pulse_limits.size(); ++i) {
        derived.push_back({SdfDelayEntryKind::kPulseLimit, i});
      }
      for (uint32_t i = 0; i < cell.interconnects.size(); ++i) {
        derived.push_back({SdfDelayEntryKind::kInterconnect, i});
      }
      order = &derived;
    }
    for (const auto& entry : *order) {
      switch (entry.kind) {
        case SdfDelayEntryKind::kIopath: {
          const auto& io = cell.iopaths[entry.index];
          PathDelay pd;
          pd.src_port = io.src_port;
          pd.dst_port = io.dst_port;

          pd.condition = io.condition;
          pd.is_ifnone = io.is_ifnone;

          {
            const auto expanded =
                ExpandSdfDelays({io.rise, io.fall, io.turnoff}, mtm);
            pd.delay_count = 12;
            for (int i = 0; i < 12; ++i) pd.delays[i] = expanded[i];
          }
          if (!io.extended_form) {
            if (io.is_increment) {
              mgr.IncrementPathDelay(pd);
              break;
            }

            ApplyGlobalPulseLimits(pd, mgr.RejectPulseLimitPercent(),
                                   mgr.ErrorPulseLimitPercent());
            mgr.AddPathDelay(pd);
            break;
          }

          const bool any_pulse_supplied =
              io.rise_reject_present || io.rise_error_present ||
              io.fall_reject_present || io.fall_error_present;
          if (!any_pulse_supplied) {
            mgr.AddPathDelay(pd, true);
            break;
          }

          ApplyGlobalPulseLimits(pd, mgr.RejectPulseLimitPercent(),
                                 mgr.ErrorPulseLimitPercent());
          if (io.rise_reject_present || io.fall_reject_present) {
            const SdfDelayValue& src_dv =
                io.rise_reject_present ? io.rise_reject : io.fall_reject;
            const uint64_t reject = SelectMtm(src_dv, mtm);
            for (int i = 0; i < 12; ++i) pd.reject_limit[i] = reject;
          }
          if (io.rise_error_present || io.fall_error_present) {
            const SdfDelayValue& src_dv =
                io.rise_error_present ? io.rise_error : io.fall_error;
            const uint64_t err = SelectMtm(src_dv, mtm);
            for (int i = 0; i < 12; ++i) pd.error_limit[i] = err;
          }
          mgr.AddPathDelay(pd);
          break;
        }
        case SdfDelayEntryKind::kPulseLimit: {
          const auto& pl = cell.pulse_limits[entry.index];

          mgr.AddSdfPulseLimit(pl.src_port, pl.dst_port,
                               SelectMtm(pl.reject, mtm), pl.has_error,
                               SelectMtm(pl.error, mtm), pl.is_percent);
          break;
        }
        case SdfDelayEntryKind::kInterconnect: {
          const auto& ic = cell.interconnects[entry.index];
          InterconnectDelay delay;
          delay.src_port = ic.src_port;
          delay.dst_port = ic.dst_port;
          delay.rise = SelectMtm(ic.rise, mtm);
          delay.fall = SelectMtm(ic.fall, mtm);

          const bool fall_supplied = ic.fall.min_val != 0 ||
                                     ic.fall.typ_val != 0 ||
                                     ic.fall.max_val != 0;
          std::vector<SdfDelayValue> ic_vals;
          ic_vals.push_back(ic.rise);
          if (fall_supplied) ic_vals.push_back(ic.fall);
          const auto expanded = ExpandSdfDelays(ic_vals, mtm);
          for (int i = 0; i < 12; ++i) {
            delay.delays[i] = expanded[i];

            delay.reject_limit[i] = expanded[i];
            delay.error_limit[i] = expanded[i];
          }

          if (ic.is_increment) {
            mgr.IncrementInterconnectDelay(delay);
            break;
          }
          mgr.AddInterconnectDelay(std::move(delay));
          break;
        }
      }
    }
    for (const auto& sp : cell.specparams) {
      SpecparamValue value;
      value.name = sp.name;
      value.value = SelectMtm(sp.value, mtm);

      if (sp.is_increment) {
        mgr.IncrementSpecparamValue(std::move(value));
      } else {
        mgr.SetSpecparamValue(std::move(value));
      }
    }
    for (const auto& tc : cell.timing_checks) {
      for (const auto& target : ExpandSdfTimingCheckTargets(tc, mtm)) {
        mgr.AnnotateSdfTimingCheck(target);
      }
    }
  }
  return result;
}

bool ParseSdfMtmKeyword(std::string_view text, SdfMtmKeyword& out) {
  if (text == "MAXIMUM") {
    out = SdfMtmKeyword::kMaximum;
    return true;
  }
  if (text == "MINIMUM") {
    out = SdfMtmKeyword::kMinimum;
    return true;
  }
  if (text == "TYPICAL") {
    out = SdfMtmKeyword::kTypical;
    return true;
  }
  if (text == "TOOL_CONTROL") {
    out = SdfMtmKeyword::kToolControl;
    return true;
  }
  return false;
}

SdfMtm ResolveSdfMtm(SdfMtmKeyword keyword, SdfMtm tool_default) {
  switch (keyword) {
    case SdfMtmKeyword::kMaximum:
      return SdfMtm::kMaximum;
    case SdfMtmKeyword::kMinimum:
      return SdfMtm::kMinimum;
    case SdfMtmKeyword::kTypical:
      return SdfMtm::kTypical;
    case SdfMtmKeyword::kToolControl:
      return tool_default;
  }
  return tool_default;
}

bool ParseSdfScaleType(std::string_view text, SdfScaleType& out) {
  if (text == "FROM_MTM") {
    out = SdfScaleType::kFromMtm;
    return true;
  }
  if (text == "FROM_MAXIMUM") {
    out = SdfScaleType::kFromMaximum;
    return true;
  }
  if (text == "FROM_MINIMUM") {
    out = SdfScaleType::kFromMinimum;
    return true;
  }
  if (text == "FROM_TYPICAL") {
    out = SdfScaleType::kFromTypical;
    return true;
  }
  return false;
}

static bool ParseRealAt(std::string_view text, std::size_t& pos, double& out) {
  while (pos < text.size() &&
         std::isspace(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
  }
  std::size_t start = pos;
  if (pos < text.size() && (text[pos] == '+' || text[pos] == '-')) ++pos;
  bool saw_digit = false;
  while (pos < text.size() &&
         std::isdigit(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
    saw_digit = true;
  }
  if (pos < text.size() && text[pos] == '.') {
    ++pos;
    while (pos < text.size() &&
           std::isdigit(static_cast<unsigned char>(text[pos])) != 0) {
      ++pos;
      saw_digit = true;
    }
  }
  if (!saw_digit) return false;
  out = std::stod(std::string(text.substr(start, pos - start)));
  return true;
}

bool ParseSdfScaleFactors(std::string_view text, SdfScaleFactors& out) {
  out = SdfScaleFactors{};
  if (text.empty()) return true;
  std::size_t pos = 0;
  double v = 0.0;
  if (!ParseRealAt(text, pos, v)) return false;
  out.min_factor = v;
  out.typ_factor = v;
  out.max_factor = v;
  while (pos < text.size() &&
         std::isspace(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
  }
  if (pos >= text.size() || text[pos] != ':') return true;
  ++pos;
  if (!ParseRealAt(text, pos, v)) return false;
  out.typ_factor = v;
  out.max_factor = v;
  while (pos < text.size() &&
         std::isspace(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
  }
  if (pos >= text.size() || text[pos] != ':') return true;
  ++pos;
  if (!ParseRealAt(text, pos, v)) return false;
  out.max_factor = v;
  return true;
}

static uint64_t RoundToTicks(double scaled) {
  if (scaled <= 0.0) return 0;
  return static_cast<uint64_t>(std::floor(scaled + 0.5));
}

SdfDelayValue ApplySdfScaling(SdfDelayValue value, SdfScaleType type,
                              const SdfScaleFactors& factors) {
  double src_min = 0.0;
  double src_typ = 0.0;
  double src_max = 0.0;
  switch (type) {
    case SdfScaleType::kFromMtm:
      src_min = static_cast<double>(value.min_val);
      src_typ = static_cast<double>(value.typ_val);
      src_max = static_cast<double>(value.max_val);
      break;
    case SdfScaleType::kFromMinimum:
      src_min = src_typ = src_max = static_cast<double>(value.min_val);
      break;
    case SdfScaleType::kFromTypical:
      src_min = src_typ = src_max = static_cast<double>(value.typ_val);
      break;
    case SdfScaleType::kFromMaximum:
      src_min = src_typ = src_max = static_cast<double>(value.max_val);
      break;
  }
  SdfDelayValue out;
  out.min_val = RoundToTicks(src_min * factors.min_factor);
  out.typ_val = RoundToTicks(src_typ * factors.typ_factor);
  out.max_val = RoundToTicks(src_max * factors.max_factor);
  return out;
}

SdfFile ScaleSdfFile(const SdfFile& file, SdfScaleType type,
                     const SdfScaleFactors& factors) {
  SdfFile out = file;
  for (auto& cell : out.cells) {
    for (auto& io : cell.iopaths) {
      io.rise = ApplySdfScaling(io.rise, type, factors);
      io.fall = ApplySdfScaling(io.fall, type, factors);
      io.turnoff = ApplySdfScaling(io.turnoff, type, factors);
      io.rise_reject = ApplySdfScaling(io.rise_reject, type, factors);
      io.rise_error = ApplySdfScaling(io.rise_error, type, factors);
      io.fall_reject = ApplySdfScaling(io.fall_reject, type, factors);
      io.fall_error = ApplySdfScaling(io.fall_error, type, factors);
    }
    for (auto& tc : cell.timing_checks) {
      tc.limit = ApplySdfScaling(tc.limit, type, factors);
      tc.limit2 = ApplySdfScaling(tc.limit2, type, factors);
    }
    for (auto& sp : cell.specparams) {
      sp.value = ApplySdfScaling(sp.value, type, factors);
    }
    for (auto& ic : cell.interconnects) {
      ic.rise = ApplySdfScaling(ic.rise, type, factors);
      ic.fall = ApplySdfScaling(ic.fall, type, factors);
    }
    for (auto& pl : cell.pulse_limits) {
      pl.reject = ApplySdfScaling(pl.reject, type, factors);
      pl.error = ApplySdfScaling(pl.error, type, factors);
    }
  }
  return out;
}

bool WriteSdfAnnotationLog(const SdfFile& file, std::string_view log_path) {
  if (log_path.empty()) return true;
  std::ofstream out{std::string(log_path)};
  if (!out.is_open()) return false;

  for (const auto& cell : file.cells) {
    const std::string prefix = cell.cell_type + "/" + cell.instance + ": ";
    for (const auto& io : cell.iopaths) {
      out << prefix << "IOPATH " << io.src_port << " -> " << io.dst_port
          << " rise=" << io.rise.typ_val << " fall=" << io.fall.typ_val << '\n';
    }
    for (const auto& ic : cell.interconnects) {
      out << prefix << "INTERCONNECT " << ic.src_port << " -> " << ic.dst_port
          << " rise=" << ic.rise.typ_val << " fall=" << ic.fall.typ_val << '\n';
    }
    for (const auto& pl : cell.pulse_limits) {
      out << prefix << "PATHPULSE " << pl.src_port << " -> " << pl.dst_port
          << " reject=" << pl.reject.typ_val << " error=" << pl.error.typ_val
          << '\n';
    }
    for (const auto& tc : cell.timing_checks) {
      out << prefix << "TIMINGCHECK " << tc.data_port << " ref=" << tc.ref_port
          << " limit=" << tc.limit.typ_val << '\n';
    }
    for (const auto& sp : cell.specparams) {
      out << prefix << "SPECPARAM " << sp.name << " value=" << sp.value.typ_val
          << '\n';
    }
  }
  return true;
}

ResolvedSdfAnnotateArgs ResolveSdfAnnotateArgs(
    std::string_view explicit_mtm_spec, std::string_view explicit_scale_factors,
    std::string_view explicit_scale_type, const SdfAnnotateConfig& config) {
  ResolvedSdfAnnotateArgs out;

  if (!config.mtm_spec.empty()) {
    ParseSdfMtmKeyword(config.mtm_spec, out.mtm);
  }
  if (!explicit_mtm_spec.empty()) {
    ParseSdfMtmKeyword(explicit_mtm_spec, out.mtm);
  }

  if (!config.scale_factors.empty()) {
    ParseSdfScaleFactors(config.scale_factors, out.factors);
  }
  if (!explicit_scale_factors.empty()) {
    ParseSdfScaleFactors(explicit_scale_factors, out.factors);
  }

  if (!config.scale_type.empty()) {
    ParseSdfScaleType(config.scale_type, out.scale_type);
  }
  if (!explicit_scale_type.empty()) {
    ParseSdfScaleType(explicit_scale_type, out.scale_type);
  }

  return out;
}

}  // namespace delta
