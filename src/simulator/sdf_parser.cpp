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
  // §32.4.2 Table 32-2: BIDIRECTSKEW exists only in SDF; the annotator
  // routes it to $fullskew per the table.
  if (name == "BIDIRECTSKEW") return SdfCheckType::kBidirectskew;
  if (name == "NOCHANGE") return SdfCheckType::kNochange;
  return SdfCheckType::kSetup;
}

// =============================================================================
// Parse SDF timing check signal (possibly with edge)
// =============================================================================

struct SdfSignalRef {
  std::string port;
  SpecifyEdge edge = SpecifyEdge::kNone;
  // §32.4.2 paragraph 3: when an SDF timing check signal is wrapped in
  // a (COND <expr> <port>) form, the wrapped expression text travels
  // here so the annotator can compare it against the SystemVerilog
  // timing check's `&&&` condition. Empty when no COND wrapper is
  // present, leaving the signal unrestricted on condition.
  std::string condition;
};

static SdfSignalRef ParseSdfSignal(std::string_view& s) {
  SdfSignalRef ref;
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    Expect(s, SdfTokKind::kLParen);
    auto first_tok = NextSdfToken(s);
    // §32.4.2 paragraph 3 example (page 928) uses
    // `(COND !mode (posedge clk))` to attach a condition to a
    // reference signal. Capture the condition text and then descend
    // into the wrapped port_instance, which itself may carry an edge.
    if (first_tok.text == "COND") {
      ref.condition = ParseSdfConditionText(s);
      SkipWhitespace(s);
      if (!s.empty() && s[0] == '(') {
        Expect(s, SdfTokKind::kLParen);
        auto edge_tok = NextSdfToken(s);
        if (edge_tok.text == "posedge") ref.edge = SpecifyEdge::kPosedge;
        else if (edge_tok.text == "negedge") ref.edge = SpecifyEdge::kNegedge;
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

// =============================================================================
// Parse a single timing check
// =============================================================================

static SdfTimingCheck ParseOneTc(std::string_view& s, SdfCheckType type) {
  SdfTimingCheck tc;
  tc.check_type = type;
  // §32.4.2 Table 32-2 single-signal kinds — WIDTH and PERIOD reference
  // one signal only and have no separate data port. Every other kind in
  // the table parses both a data and a reference port.
  const bool single_signal = (type == SdfCheckType::kWidth ||
                              type == SdfCheckType::kPeriod);
  auto first = ParseSdfSignal(s);
  if (single_signal) {
    tc.ref_port = first.port;
    tc.ref_edge = first.edge;
    // §32.4.2 paragraph 3: a COND wrapper around the single signal
    // attaches a condition to the only signal the check has, which is
    // by definition the reference signal (WIDTH and PERIOD have no
    // separate data signal). Propagate so the matcher sees it.
    tc.condition = std::move(first.condition);
  } else {
    tc.data_port = first.port;
    tc.data_edge = first.edge;
    auto ref = ParseSdfSignal(s);
    tc.ref_port = ref.port;
    tc.ref_edge = ref.edge;
    // §32.4.2 paragraph 3: SystemVerilog timing checks attach the `&&&`
    // condition to the reference event only, so an SDF condition that
    // appears on the reference signal is the one the matcher consults.
    // Conditions parsed off the data signal (rare in practice and not
    // used by the LRM examples) would have nowhere to land in
    // TimingCheckEntry, so they are dropped here.
    tc.condition = std::move(ref.condition);
  }
  tc.limit = ParseDelayVal(s);
  // §32.4.2 Table 32-2 two-value kinds — SETUPHOLD, RECREM, BIDIRECTSKEW,
  // NOCHANGE supply v2 in addition to v1. Defaulted to a zero-valued
  // triplet for the other kinds where the table only references v1.
  const bool two_value = (type == SdfCheckType::kSetuphold ||
                          type == SdfCheckType::kRecrem ||
                          type == SdfCheckType::kBidirectskew ||
                          type == SdfCheckType::kNochange);
  if (two_value) {
    SkipWhitespace(s);
    if (!s.empty() && s[0] == '(') {
      tc.limit2 = ParseDelayVal(s);
    }
  }
  Expect(s, SdfTokKind::kRParen);
  return tc;
}

// =============================================================================
// Parse DELAY section
// =============================================================================

// §32.4.4 Table 32-3: parse the body of an (INTERCONNECT src dst delays...)
// block. The caller has already consumed the leading `(` and the
// INTERCONNECT keyword, so this helper expects to see the source port,
// the destination port, and a delay list of one or two triplets, then
// close the construct's own `)`. Source and destination travel verbatim
// onto the SdfInterconnect so a downstream stage can validate them
// against the netlist (the LRM requires source = output/inout and
// destination = input/inout, with a warn-but-still-annotate fall-through
// when the source port is unknown or the two endpoints are not on the
// same net).
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

// §32.4.4 Table 32-3: parse a (PORT load delays...) or
// (NETDELAY load delays...) block. Both shapes name only the load port
// because the LRM defines their semantics as the delay from all sources
// on the net to the load — there is no per-entry source. The caller has
// already consumed the leading `(` and the keyword, and supplies the
// kind so the same helper covers both rows of Table 32-3 without
// duplicating the parse.
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
    // §32.4.4 Table 32-3: INTERCONNECT/PORT/NETDELAY all map to interconnect
    // delays. Decode them into typed SdfInterconnect entries — they belong
    // to backannotation, not the §32.3 unannotatable warning channel.
    if (kw.text == "INTERCONNECT") {
      cell.interconnects.push_back(ParseInterconnectEntry(s));
      continue;
    }
    if (kw.text == "PORT") {
      cell.interconnects.push_back(
          ParseLoadOnlyInterconnect(s, SdfInterconnectKind::kPort));
      continue;
    }
    if (kw.text == "NETDELAY") {
      cell.interconnects.push_back(
          ParseLoadOnlyInterconnect(s, SdfInterconnectKind::kNetdelay));
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

// §32.4.3: a LABEL specparam value follows the SDF rvalue grammar, which
// admits both a wrapped triplet `(N:N:N)` / single `(N)` and a bare
// `signed_real_number` form. The page-927 LRM example writes `(dhigh 60)`
// — bare-number form — so the parser must accept either shape rather than
// always demanding the parenthesised triplet `ParseDelayVal` consumes.
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

// §32.4.3 sentence 1: the LABEL section's `(identifier delval)` entries
// each name a SystemVerilog specparam to update. Decode every such pair
// into an SdfSpecparam on the cell so the downstream annotator can route
// the new value through SetSpecparamValue. The caller has consumed the
// outer `(LABEL` parens and a leading `(`, leaving the ABSOLUTE/INCREMENT
// keyword to be read here, after which we walk the body until its closing
// `)` and then consume LABEL's own closing `)`.
static void ParseLabelSection(std::string_view& s, SdfCell& cell,
                              SdfFile& file) {
  SkipWhitespace(s);
  if (s.empty() || s[0] != '(') {
    // Empty LABEL body — nothing to decode and nothing to warn about.
    Expect(s, SdfTokKind::kRParen);
    return;
  }
  Expect(s, SdfTokKind::kLParen);
  auto mode = NextSdfToken(s);
  // The ABSOLUTE/INCREMENT distinction is part of the SDF grammar but the
  // §32.4.3 text only describes the ABSOLUTE form; INCREMENT entries are
  // surfaced through the §32.3 warning channel rather than silently
  // mis-applied as ABSOLUTE values.
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
    Expect(s, SdfTokKind::kRParen);
    if (increment) {
      // INCREMENT semantics on specparams are outside §32.4.3's text;
      // record so the warning channel surfaces the omission rather than
      // dropping the value silently.
      file.unannotatable.emplace_back("LABEL");
      continue;
    }
    cell.specparams.push_back(std::move(sp));
  }
  Expect(s, SdfTokKind::kRParen);  // close ABSOLUTE/INCREMENT
  Expect(s, SdfTokKind::kRParen);  // close LABEL
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
      ParseLabelSection(s, cell, file);
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

// §32.4.2 Table 32-2: expand one SDF timing check construct into the list
// of SystemVerilog timing checks the row dictates. Each target carries
// per-field `set_*` flags that distinguish a real value from the table's
// "x" marker so the matched SystemVerilog entry's other fields keep
// their prebackannotation values.
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
      // Table row "(SETUP v1...) → $setup(v1), $setuphold(v1,x)"
      auto& s = push(TimingCheckKind::kSetup);
      s.set_limit = true;
      s.limit = v1;
      auto& sh = push(TimingCheckKind::kSetuphold);
      sh.set_limit = true;
      sh.limit = v1;
      break;
    }
    case SdfCheckType::kHold: {
      // Table row "(HOLD v1...) → $hold(v1), $setuphold(x,v1)"
      auto& h = push(TimingCheckKind::kHold);
      h.set_limit = true;
      h.limit = v1;
      auto& sh = push(TimingCheckKind::kSetuphold);
      sh.set_limit2 = true;
      sh.limit2 = v1;
      break;
    }
    case SdfCheckType::kSetuphold: {
      // Table row "(SETUPHOLD v1 v2...) → $setup(v1), $hold(v2),
      // $setuphold(v1,v2)"
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
      // Table row "(RECOVERY v1...) → $recovery(v1), $recrem(v1,x)"
      auto& r = push(TimingCheckKind::kRecovery);
      r.set_limit = true;
      r.limit = v1;
      auto& rr = push(TimingCheckKind::kRecrem);
      rr.set_limit = true;
      rr.limit = v1;
      break;
    }
    case SdfCheckType::kRemoval: {
      // Table row "(REMOVAL v1...) → $removal(v1), $recrem(x,v1)"
      auto& r = push(TimingCheckKind::kRemoval);
      r.set_limit = true;
      r.limit = v1;
      auto& rr = push(TimingCheckKind::kRecrem);
      rr.set_limit2 = true;
      rr.limit2 = v1;
      break;
    }
    case SdfCheckType::kRecrem: {
      // Table row "(RECREM v1 v2...) → $recovery(v1), $removal(v2),
      // $recrem(v1,v2)"
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
      // Table row "(SKEW v1...) → $skew(v1), $timeskew(v1)"
      auto& s = push(TimingCheckKind::kSkew);
      s.set_limit = true;
      s.limit = v1;
      auto& ts = push(TimingCheckKind::kTimeskew);
      ts.set_limit = true;
      ts.limit = v1;
      break;
    }
    case SdfCheckType::kBidirectskew: {
      // Table row "(BIDIRECTSKEW v1 v2...) → $fullskew(v1,v2)"
      auto& fs = push(TimingCheckKind::kFullskew);
      fs.set_limit = true;
      fs.limit = v1;
      fs.set_limit2 = true;
      fs.limit2 = v2;
      break;
    }
    case SdfCheckType::kWidth: {
      // Table row "(WIDTH v1...) → $width(v1,x)" — the x is $width's
      // glitch threshold, which §31.4.4 stores on a separate field; we
      // only ever write `limit` so the threshold survives the pass.
      auto& w = push(TimingCheckKind::kWidth);
      w.set_limit = true;
      w.limit = v1;
      break;
    }
    case SdfCheckType::kPeriod: {
      // Table row "(PERIOD v1...) → $period(v1)"
      auto& p = push(TimingCheckKind::kPeriod);
      p.set_limit = true;
      p.limit = v1;
      break;
    }
    case SdfCheckType::kNochange: {
      // Table row "(NOCHANGE v1 v2...) → $nochange(v1,v2)" — §31.4.6
      // names $nochange's two arguments start_edge_offset and
      // end_edge_offset, which TimingCheckEntry stores on dedicated
      // signed fields rather than `limit` / `limit2`.
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
      // §32.4.2: route through Table 32-2 — one SDF construct may produce
      // several SystemVerilog timing-check annotations, each with its own
      // per-field "x" mask. Per-target installation goes through
      // AnnotateSdfTimingCheck so paragraph 2's match-by-property rule
      // applies uniformly.
      for (const auto& target : ExpandSdfTimingCheckTargets(tc, mtm)) {
        mgr.AnnotateSdfTimingCheck(target);
      }
    }
    for (const auto& ic : cell.interconnects) {
      InterconnectDelay delay;
      delay.src_port = ic.src_port;
      delay.dst_port = ic.dst_port;
      delay.rise = SelectMtm(ic.rise, mtm);
      delay.fall = SelectMtm(ic.fall, mtm);
      // §32.4.4: interconnect delays follow the same fill-in rules as
      // specify path delays. Borrow the §30.5.1 / Table 30-2 expansion
      // helper by staging the rise and fall values inside a PathDelay,
      // letting ExpandTransitionDelays produce the twelve-slot result,
      // then copy the slots out. A purely-zero fall (the LRM's
      // single-value SDF input) keeps `delay_count` at 1 so the
      // expansion broadcasts the rise value across every slot; a
      // supplied fall switches to the two-value column in which rise
      // covers the 0->z/z->1 transitions and fall covers 1->z/z->0.
      PathDelay scratch;
      scratch.delays[0] = delay.rise;
      const bool fall_supplied = ic.fall.min_val != 0 || ic.fall.typ_val != 0 ||
                                 ic.fall.max_val != 0;
      if (fall_supplied) {
        scratch.delays[1] = delay.fall;
        scratch.delay_count = 2;
      } else {
        scratch.delay_count = 1;
      }
      ExpandTransitionDelays(scratch);
      for (int i = 0; i < 12; ++i) {
        delay.delays[i] = scratch.delays[i];
        // §32.4.4: each of the twelve transition delays carries its own
        // reject and error pulse limit. Initialise both to the matching
        // delay so the default inertial-delay behaviour applies — a
        // pulse narrower than the propagation delay is rejected — until
        // a later mechanism revises the limits.
        delay.reject_limit[i] = scratch.delays[i];
        delay.error_limit[i] = scratch.delays[i];
      }
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
