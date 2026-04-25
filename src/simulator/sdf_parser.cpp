// IEEE 1800-2023 §32 — SDF parser and annotation engine.

#include "simulator/sdf_parser.h"

#include <algorithm>
#include <cctype>

#include "simulator/specify.h"

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

// §32.4.1: capture the SDF condition expression that follows COND. The LRM
// describes it as a Verilog-style boolean expression, but the only thing
// the annotator needs is the textual form: it is compared character-wise
// against the matching SystemVerilog `if (cond)` text on PathDelay. So the
// parser collects every token up to the next opening parenthesis (which
// starts the wrapped IOPATH) and joins them with single spaces — preserving
// inter-token boundaries while throwing away whatever whitespace the SDF
// source happened to use.
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

// =============================================================================
// Parse IOPATH
// =============================================================================

static SdfIopath ParseIopath(std::string_view& s) {
  SdfIopath io;
  io.src_port = ParseSdfPort(s);
  io.dst_port = ParseSdfPort(s);
  // §32.4.1 Table 32-1 RETAIN rows: a (RETAIN ...) directive may appear
  // between the destination port and the rise/fall/turnoff delay triplets.
  // The table allows the simulator to ignore RETAIN entirely. Detect the
  // construct by peeking for a `(RETAIN` opener and skip the parenthesised
  // block so the following ParseDelayVal calls land on the actual delay
  // values rather than mis-tokenising the RETAIN body as a delay number.
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

// §32.4.1 Table 32-1 PATHPULSE / PATHPULSEPERCENT: parse the body of a
// (PATHPULSE src dst (reject) [(error)]) or PATHPULSEPERCENT block. The
// caller has already consumed the leading `(` and the keyword token, so
// this helper expects to see the source/destination ports followed by
// one or two delay-value triplets, then close the construct's `)`. The
// returned entry's `is_percent` flag is set by the caller.
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

static void ParseDelaySection(std::string_view& s, SdfCell& cell, SdfFile& file,
                              bool increment) {
  // Inside (ABSOLUTE ...) or (INCREMENT ...)
  while (true) {
    SkipWhitespace(s);
    if (s.empty() || s[0] == ')') break;
    Expect(s, SdfTokKind::kLParen);
    auto kw = NextSdfToken(s);
    if (kw.text == "PATHPULSE" || kw.text == "PATHPULSEPERCENT") {
      auto pl = ParsePulseLimit(s);
      pl.is_percent = (kw.text == "PATHPULSEPERCENT");
      cell.pulse_limits.push_back(pl);
      continue;
    }
    if (kw.text == "IOPATH") {
      auto io = ParseIopath(s);
      io.is_increment = increment;
      cell.iopaths.push_back(io);
    } else if (kw.text == "COND") {
      // §32.4.1 Table 32-1 row "(COND (IOPATH...)": the wrapper carries a
      // condition expression followed by an IOPATH. Capture the condition
      // text, then descend into the IOPATH and stamp the iopath with it.
      // A malformed COND that contains no nested IOPATH is treated as an
      // unannotatable construct so the §32.3 warning channel remains the
      // single home for things the parser sees but cannot map.
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
          Expect(s, SdfTokKind::kRParen);  // close COND
          continue;
        }
        // Unknown nested construct under COND — fall through to the
        // generic skip path so the warning channel still surfaces it.
        SkipSdfParen(s);
      }
      file.unannotatable.emplace_back("COND");
      // Close the outer COND parens that the surrounding loop expected to
      // be balanced when it took the leading '('. We may already be on
      // ')' if the inner branch consumed only the inner pair, so probe
      // gently rather than insisting on a paren here.
      SkipWhitespace(s);
      if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
    } else if (kw.text == "CONDELSE") {
      // §32.4.1 Table 32-1 row "(CONDELSE (IOPATH...) → ifnone": no
      // condition expression — CONDELSE always means "the SV ifnone
      // specify path between these two ports".
      SkipWhitespace(s);
      if (!s.empty() && s[0] == '(') {
        Expect(s, SdfTokKind::kLParen);
        auto inner = NextSdfToken(s);
        if (inner.text == "IOPATH") {
          auto io = ParseIopath(s);
          io.is_increment = increment;
          io.is_ifnone = true;
          cell.iopaths.push_back(io);
          Expect(s, SdfTokKind::kRParen);  // close CONDELSE
          continue;
        }
        SkipSdfParen(s);
      }
      file.unannotatable.emplace_back("CONDELSE");
      SkipWhitespace(s);
      if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
    } else {
      // §32.3: this construct sits inside DELAY — i.e. it is one of the
      // §32.2 path-delay categories — but the parser cannot decode it.
      // Record so the annotator can warn rather than dropping silently.
      file.unannotatable.emplace_back(kw.text);
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
// Parse LABEL section
// =============================================================================

// §32.4: LABEL is one of the three CELL sections SDF timing values appear
// within (alongside DELAY and TIMINGCHECK), and §32.4 sentence 4 assigns its
// contents to the specparam-value backannotation category. The detailed
// mapping from LABEL name-value entries to specparams belongs to §32.4.3;
// recognising LABEL here lets §32.3 sentence 1 surface a warning for the
// section's contents instead of silently dropping it the way the parser
// drops constructs unrelated to SystemVerilog timing.
static void ParseLabelSection(std::string_view& s, SdfFile& file) {
  file.unannotatable.emplace_back("LABEL");
  SkipSdfParen(s);
}

// =============================================================================
// Parse a CELL
// =============================================================================

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
      ParseLabelSection(s, file);
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
      out.cells.push_back(ParseCell(input, out));
    } else {
      // §32.3: at the DELAYFILE level, anything besides CELL/SDFVERSION/
      // DESIGN is either header metadata (DATE, VENDOR, PROGRAM, ...) or
      // a TIMINGENV section — in either case "unrelated to SystemVerilog
      // timing" per §32.3, so it is dropped silently with no warning.
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

SdfAnnotationResult AnnotateSdfToManager(const SdfFile& file,
                                         SpecifyManager& mgr, SdfMtm mtm) {
  SdfAnnotationResult result;
  // §32.3 sentence 1: surface one warning per piece of SDF data the
  // parser flagged as unannotatable. Constructs unrelated to
  // SystemVerilog timing never reach this list (see SdfFile::unannotatable),
  // so §32.3's silent-ignore rule for TIMINGENV and similar sections is
  // preserved.
  for (const auto& kw : file.unannotatable) {
    result.warnings.push_back("SDF annotator: unable to annotate " + kw +
                              " construct");
  }
  // §32.2: backannotation iterates each of the four named categories. The
  // chosen MTM column is applied uniformly so a single invocation produces
  // a self-consistent timing snapshot. §32.3 sentence 4: only categories
  // mentioned by the SDF file are written, so any pre-existing manager
  // entry the file does not name is left at its prebackannotation value.
  for (const auto& cell : file.cells) {
    for (const auto& io : cell.iopaths) {
      PathDelay pd;
      pd.src_port = io.src_port;
      pd.dst_port = io.dst_port;
      // §32.4.1: forward the SDF condition / ifnone flag so AddPathDelay
      // can route the entry under the LRM's conditional vs nonconditional
      // matching rules. A bare IOPATH leaves both fields at their defaults
      // (empty string, false) and dispatches as nonconditional.
      pd.condition = io.condition;
      pd.is_ifnone = io.is_ifnone;
      pd.delay_count = 3;
      pd.delays[0] = SelectMtm(io.rise, mtm);
      pd.delays[1] = SelectMtm(io.fall, mtm);
      pd.delays[2] = SelectMtm(io.turnoff, mtm);
      mgr.AddPathDelay(pd);
    }
    for (const auto& sp : cell.specparams) {
      SpecparamValue value;
      value.name = sp.name;
      value.value = SelectMtm(sp.value, mtm);
      mgr.SetSpecparamValue(std::move(value));
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
    for (const auto& ic : cell.interconnects) {
      InterconnectDelay delay;
      delay.src_port = ic.src_port;
      delay.dst_port = ic.dst_port;
      delay.rise = SelectMtm(ic.rise, mtm);
      delay.fall = SelectMtm(ic.fall, mtm);
      mgr.AddInterconnectDelay(std::move(delay));
    }
    for (const auto& pl : cell.pulse_limits) {
      // §32.4.1 Table 32-1 PATHPULSE / PATHPULSEPERCENT: route the parsed
      // entry through the manager helper that fans the limits across all
      // matching specify paths, regardless of their condition. The
      // percent/absolute distinction is preserved on the SdfPulseLimit
      // and dispatched inside the manager.
      mgr.AddSdfPulseLimit(pl.src_port, pl.dst_port, SelectMtm(pl.reject, mtm),
                           pl.has_error, SelectMtm(pl.error, mtm),
                           pl.is_percent);
    }
  }
  return result;
}

}  // namespace delta
