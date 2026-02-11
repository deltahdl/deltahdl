// IEEE 1800-2023 §32 — SDF parser and annotation engine.

#include "simulation/sdf_parser.h"

#include <algorithm>
#include <cctype>

#include "simulation/specify.h"

namespace delta {

// =============================================================================
// SDF lexer: tokenize parentheses, keywords, strings, numbers
// =============================================================================

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
  s.remove_prefix(1);  // skip opening '"'
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

// =============================================================================
// SDF parser helpers
// =============================================================================

static bool Expect(std::string_view& s, SdfTokKind kind) {
  auto tok = NextSdfToken(s);
  return tok.kind == kind;
}

static SdfDelayValue ParseDelayVal(std::string_view& s) {
  SdfDelayValue dv;
  // Expect '('
  if (!Expect(s, SdfTokKind::kLParen)) return dv;
  auto first = NextSdfToken(s);
  if (first.kind == SdfTokKind::kNumber) {
    dv.min_val = first.num_val;
    dv.typ_val = first.num_val;
    dv.max_val = first.num_val;
    // Check for :typ:max
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
  // Port might be bare identifier or (edge identifier)
  if (!s.empty() && s[0] == '(') {
    // Edge-qualified port: handled by caller
    return "";
  }
  auto tok = NextSdfToken(s);
  return std::string(tok.text);
}

// Skip to matching closing paren.
static void SkipSdfParen(std::string_view& s) {
  int depth = 1;
  while (depth > 0 && !s.empty()) {
    auto tok = NextSdfToken(s);
    if (tok.kind == SdfTokKind::kLParen) ++depth;
    if (tok.kind == SdfTokKind::kRParen) --depth;
    if (tok.kind == SdfTokKind::kEof) break;
  }
}

// =============================================================================
// Parse IOPATH
// =============================================================================

static SdfIopath ParseIopath(std::string_view& s) {
  SdfIopath io;
  io.src_port = ParseSdfPort(s);
  io.dst_port = ParseSdfPort(s);
  io.rise = ParseDelayVal(s);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    io.fall = ParseDelayVal(s);
  }
  // Skip to closing paren of IOPATH
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    io.turnoff = ParseDelayVal(s);
  }
  Expect(s, SdfTokKind::kRParen);
  return io;
}

// =============================================================================
// Parse timing check keyword
// =============================================================================

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
  if (name == "NOCHANGE") return SdfCheckType::kNochange;
  return SdfCheckType::kSetup;
}

// =============================================================================
// Parse SDF timing check signal (possibly with edge)
// =============================================================================

struct SdfSignalRef {
  std::string port;
  SpecifyEdge edge = SpecifyEdge::kNone;
};

static SdfSignalRef ParseSdfSignal(std::string_view& s) {
  SdfSignalRef ref;
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    // (edge port)
    Expect(s, SdfTokKind::kLParen);
    auto edge_tok = NextSdfToken(s);
    if (edge_tok.text == "posedge") ref.edge = SpecifyEdge::kPosedge;
    if (edge_tok.text == "negedge") ref.edge = SpecifyEdge::kNegedge;
    auto port_tok = NextSdfToken(s);
    ref.port = std::string(port_tok.text);
    Expect(s, SdfTokKind::kRParen);
  } else {
    auto tok = NextSdfToken(s);
    ref.port = std::string(tok.text);
  }
  return ref;
}

// =============================================================================
// Parse a single timing check
// =============================================================================

static SdfTimingCheck ParseOneTc(std::string_view& s, SdfCheckType type) {
  SdfTimingCheck tc;
  tc.check_type = type;
  auto data = ParseSdfSignal(s);
  tc.data_port = data.port;
  tc.data_edge = data.edge;
  auto ref = ParseSdfSignal(s);
  tc.ref_port = ref.port;
  tc.ref_edge = ref.edge;
  tc.limit = ParseDelayVal(s);
  Expect(s, SdfTokKind::kRParen);
  return tc;
}

// =============================================================================
// Parse DELAY section
// =============================================================================

static void ParseDelaySection(std::string_view& s, SdfCell& cell,
                              bool increment) {
  // Inside (ABSOLUTE ...) or (INCREMENT ...)
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == ')') break;
    Expect(s, SdfTokKind::kLParen);
    auto kw = NextSdfToken(s);
    if (kw.text == "IOPATH") {
      auto io = ParseIopath(s);
      io.is_increment = increment;
      cell.iopaths.push_back(io);
    } else {
      SkipSdfParen(s);
    }
  }
  Expect(s, SdfTokKind::kRParen);
}

// =============================================================================
// Parse TIMINGCHECK section
// =============================================================================

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

// =============================================================================
// Parse a CELL
// =============================================================================

static SdfCell ParseCell(std::string_view& s) {
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
      ParseDelaySection(s, cell, inc);
      Expect(s, SdfTokKind::kRParen);
    } else if (kw.text == "TIMINGCHECK") {
      ParseTimingCheckSection(s, cell);
    } else {
      SkipSdfParen(s);
    }
  }
  Expect(s, SdfTokKind::kRParen);
  return cell;
}

// =============================================================================
// Top-level SDF parser
// =============================================================================

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
      out.cells.push_back(ParseCell(input));
    } else {
      SkipSdfParen(input);
    }
  }
  return true;
}

// =============================================================================
// Delay value selection per MTM
// =============================================================================

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

// =============================================================================
// Delay expansion (Table 32-4)
// =============================================================================

std::vector<uint64_t> ExpandSdfDelays(const std::vector<SdfDelayValue>& vals,
                                      SdfMtm mtm) {
  std::vector<uint64_t> out(12, 0);
  if (vals.empty()) return out;

  if (vals.size() == 1) {
    uint64_t v = SelectMtm(vals[0], mtm);
    std::fill(out.begin(), out.end(), v);
    return out;
  }

  uint64_t rise = SelectMtm(vals[0], mtm);
  uint64_t fall = SelectMtm(vals[1], mtm);
  uint64_t turnoff = (vals.size() >= 3) ? SelectMtm(vals[2], mtm) : 0;

  // Table 32-4: 3-value mapping
  out[0] = rise;                     // 0->1
  out[1] = fall;                     // 1->0
  out[2] = turnoff;                  // 0->z
  out[3] = rise;                     // z->1
  out[4] = turnoff;                  // 1->z
  out[5] = fall;                     // z->0
  out[6] = std::min(rise, turnoff);  // 0->x
  out[7] = std::max(rise, turnoff);  // x->1
  out[8] = std::min(fall, turnoff);  // 1->x
  out[9] = std::max(fall, turnoff);  // x->0
  out[10] = std::min(rise, fall);    // x->z
  out[11] = std::max(rise, fall);    // z->x

  return out;
}

// =============================================================================
// Annotation
// =============================================================================

static TimingCheckKind MapSdfToTcKind(SdfCheckType ct) {
  switch (ct) {
    case SdfCheckType::kSetup:
      return TimingCheckKind::kSetup;
    case SdfCheckType::kHold:
      return TimingCheckKind::kHold;
    case SdfCheckType::kSetuphold:
      return TimingCheckKind::kSetuphold;
    case SdfCheckType::kRecovery:
      return TimingCheckKind::kRecovery;
    case SdfCheckType::kRemoval:
      return TimingCheckKind::kRemoval;
    case SdfCheckType::kRecrem:
      return TimingCheckKind::kRecrem;
    case SdfCheckType::kWidth:
      return TimingCheckKind::kWidth;
    case SdfCheckType::kPeriod:
      return TimingCheckKind::kPeriod;
    case SdfCheckType::kSkew:
      return TimingCheckKind::kSkew;
    case SdfCheckType::kNochange:
      return TimingCheckKind::kNochange;
  }
  return TimingCheckKind::kSetup;
}

void AnnotateSdfToManager(const SdfFile& file, SpecifyManager& mgr,
                          SdfMtm mtm) {
  for (const auto& cell : file.cells) {
    for (const auto& io : cell.iopaths) {
      PathDelay pd;
      pd.src_port = io.src_port;
      pd.dst_port = io.dst_port;
      pd.rise_delay = SelectMtm(io.rise, mtm);
      pd.fall_delay = SelectMtm(io.fall, mtm);
      pd.z_delay = SelectMtm(io.turnoff, mtm);
      mgr.AddPathDelay(pd);
    }
    for (const auto& tc : cell.timing_checks) {
      TimingCheckEntry entry;
      entry.kind = MapSdfToTcKind(tc.check_type);
      entry.ref_signal = tc.ref_port;
      entry.ref_edge = tc.ref_edge;
      entry.data_signal = tc.data_port;
      entry.data_edge = tc.data_edge;
      entry.limit = SelectMtm(tc.limit, mtm);
      mgr.AddTimingCheck(entry);
    }
  }
}

}  // namespace delta
