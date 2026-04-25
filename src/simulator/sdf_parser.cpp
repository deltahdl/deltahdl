// IEEE 1800-2023 §32 — SDF parser and annotation engine.

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

// §32.5 examples 2 and 3: an extended-form IOPATH direction is
// `((delay) (reject) (error))` where any of the three inner groups may
// be empty parens. ParseDelayValOrEmpty consumes one such inner group:
// it always reads the surrounding `(` and `)`, and reports through
// `*present` whether a number was actually inside. An empty group leaves
// the returned SdfDelayValue at its zero-initialised default; the
// annotator consults the matching `*_present` flag rather than the
// numeric value to honour the LRM's "hold the current values" rule.
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

// §32.5 examples 2 and 3: an extended-form direction triplet
// `((delay) (reject) (error))`. The outer parens wrap up to three inner
// groups in order; missing trailing groups are treated as absent.
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

// §32.5 examples 2 and 3: the SDF source is in extended IOPATH form when
// the first character inside the leading direction paren is itself a `(`,
// signalling the nested `((delay) (reject) (error))` shape. The simple
// form has a digit (or `:`) there. Peek without consuming so the caller
// can dispatch to the right per-direction parser.
static bool LooksLikeExtendedIopathDirection(std::string_view s) {
  if (s.empty() || s[0] != '(') return false;
  size_t i = 1;
  while (i < s.size() && (std::isspace(static_cast<unsigned char>(s[i])) != 0)) {
    ++i;
  }
  return i < s.size() && s[i] == '(';
}

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

  SkipWhitespace(s);
  io.extended_form = LooksLikeExtendedIopathDirection(s);
  if (io.extended_form) {
    // §32.5 example 3 lays out the extended form per direction:
    // `((delay) (reject) (error))`. Read up to three directions
    // (rise, fall, turnoff) and copy their components onto the
    // SdfIopath; absent groups stay at the zero-initialised default
    // and the matching `*_present` flag tells the annotator which
    // slots received a value.
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
      // The §32.5 examples don't exercise turnoff pulse-limit
      // components; only the delay value is forwarded so the existing
      // simple-form turnoff handling continues to work, while any
      // turnoff reject/error slot the source supplied is silently
      // accepted but not propagated onto the path.
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

// §32.5: append the just-parsed entry to the cell's source-order trail
// so the annotator can replay the DELAY section in the order the parser
// saw the constructs. Centralised so each push_back into a typed vector
// stays paired with the corresponding order record.
static void RecordDelayEntry(SdfCell& cell, SdfDelayEntryKind kind,
                             size_t index) {
  SdfDelayEntryRef ref;
  ref.kind = kind;
  ref.index = static_cast<uint32_t>(index);
  cell.delay_entry_order.push_back(ref);
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
      RecordDelayEntry(cell, SdfDelayEntryKind::kPulseLimit,
                       cell.pulse_limits.size() - 1);
      continue;
    }
    // §32.4.4 Table 32-3: INTERCONNECT/PORT/NETDELAY all map to interconnect
    // delays. Decode them into typed SdfInterconnect entries — they belong
    // to backannotation, not the §32.3 unannotatable warning channel.
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
          RecordDelayEntry(cell, SdfDelayEntryKind::kIopath,
                           cell.iopaths.size() - 1);
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
          RecordDelayEntry(cell, SdfDelayEntryKind::kIopath,
                           cell.iopaths.size() - 1);
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
    sp.is_increment = increment;
    Expect(s, SdfTokKind::kRParen);
    // §32.6 sentence 3: INCREMENT-mode specparams are not dropped — the
    // mode bit travels onto the SdfSpecparam so the annotator can fold
    // the new value into the running specparam total rather than
    // overwriting the prior one. ABSOLUTE leaves `is_increment` false
    // and the existing overwrite path applies.
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
// Delay expansion (§32.8 Table 32-4)
// =============================================================================

std::vector<uint64_t> ExpandSdfDelays(const std::vector<SdfDelayValue>& vals,
                                      SdfMtm mtm) {
  std::vector<uint64_t> out(12, 0);
  if (vals.empty()) return out;

  const std::size_t n = vals.size();
  const uint64_t v1 = SelectMtm(vals[0], mtm);

  // Table 32-4 enumerates exactly five input counts. Counts outside that
  // set have no LRM-defined mapping; broadcast v1 across every slot so a
  // misuse still leaves the path table populated rather than half-zero.
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
    out[0] = v1;                    // 0->1
    out[1] = v2;                    // 1->0
    out[2] = v1;                    // 0->z
    out[3] = v1;                    // z->1
    out[4] = v2;                    // 1->z
    out[5] = v2;                    // z->0
    out[6] = v1;                    // 0->x
    out[7] = v1;                    // x->1
    out[8] = v2;                    // 1->x
    out[9] = v2;                    // x->0
    out[10] = std::max(v1, v2);     // x->z
    out[11] = std::min(v1, v2);     // z->x
    return out;
  }

  const uint64_t v3 = SelectMtm(vals[2], mtm);
  if (n == 3) {
    out[0] = v1;                    // 0->1
    out[1] = v2;                    // 1->0
    out[2] = v3;                    // 0->z
    out[3] = v1;                    // z->1
    out[4] = v3;                    // 1->z
    out[5] = v2;                    // z->0
    out[6] = std::min(v1, v3);      // 0->x
    out[7] = std::max(v1, v3);      // x->1
    out[8] = std::min(v2, v3);      // 1->x
    out[9] = v2;                    // x->0
    out[10] = v3;                   // x->z
    out[11] = std::min(v1, v2);     // z->x
    return out;
  }

  const uint64_t v4 = SelectMtm(vals[3], mtm);
  const uint64_t v5 = SelectMtm(vals[4], mtm);
  const uint64_t v6 = SelectMtm(vals[5], mtm);
  if (n == 6) {
    out[0] = v1;                    // 0->1
    out[1] = v2;                    // 1->0
    out[2] = v3;                    // 0->z
    out[3] = v4;                    // z->1
    out[4] = v5;                    // 1->z
    out[5] = v6;                    // z->0
    out[6] = std::min(v1, v3);      // 0->x
    out[7] = std::max(v1, v4);      // x->1
    out[8] = std::min(v2, v5);      // 1->x
    out[9] = std::max(v2, v6);      // x->0
    out[10] = std::max(v3, v5);     // x->z
    out[11] = std::min(v4, v6);     // z->x
    return out;
  }

  // n == 12: every transition slot maps directly to the matching SDF value.
  for (std::size_t i = 0; i < 12; ++i) {
    out[i] = SelectMtm(vals[i], mtm);
  }
  return out;
}

std::array<uint64_t, 4> ReduceSdfDelaysToThree(
    const std::vector<SdfDelayValue>& vals, SdfMtm mtm) {
  std::array<uint64_t, 4> out{0, 0, 0, 0};
  if (vals.empty()) return out;
  // §32.8 sentence 5: take only the first three SDF entries, ignoring v4
  // onward. The slot fill-in for inputs of size 1 or 2 is §28.16 /
  // Table 28-9 territory; broadcast the first value as a defensive
  // populate so the X-state minimum still draws from three real values.
  out[0] = SelectMtm(vals[0], mtm);
  out[1] = vals.size() >= 2 ? SelectMtm(vals[1], mtm) : out[0];
  out[2] = vals.size() >= 3 ? SelectMtm(vals[2], mtm) : out[0];
  // §32.8 sentence 6: the X-state delay equals the minimum of the other
  // three delays.
  out[3] = std::min({out[0], out[1], out[2]});
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

// §32.6 sentence 4: decide whether a cell sits at or hierarchically under
// the named region. The scope is a hierarchical prefix; an empty scope
// disables the filter so every cell qualifies. A non-empty scope matches
// a cell whose instance equals the scope or whose first separator-
// delimited segment is exactly the scope, so "u1" includes both "u1"
// and "u1/sub/dut" but rejects sibling regions like "u10/dut" that
// merely share a leading substring. Either '/' or '.' is accepted as
// the hierarchy separator since SDF and SystemVerilog name them
// differently and no LRM rule narrows the choice.
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
  //
  // §32.5: within each cell's DELAY section, IOPATH / PATHPULSE /
  // INTERCONNECT / PORT / NETDELAY entries must be applied in the order
  // the SDF source spelled them out — a per-category iteration would
  // collapse the LRM's "ordered process" guarantee. Walk
  // `delay_entry_order` instead, dispatching on each ref's kind. For
  // SdfCell instances built programmatically (older tests still wire
  // category vectors directly) the order vector is empty; in that case
  // synthesise a category-by-category fallback so legacy callers keep
  // observing their pre-§32.5 ordering.
  for (const auto& cell : file.cells) {
    // §32.6 sentence 4: skip cells outside the caller-supplied region so
    // that "different regions of a design can be annotated from
    // different SDF files" via successive scoped calls. The empty-scope
    // default leaves every cell eligible, preserving the §32.5
    // single-call behaviour.
    if (!CellInScope(cell.instance, scope)) continue;
    std::vector<SdfDelayEntryRef> derived;
    const std::vector<SdfDelayEntryRef>* order = &cell.delay_entry_order;
    if (order->empty() && (!cell.iopaths.empty() ||
                            !cell.pulse_limits.empty() ||
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
          // §32.4.1: forward the SDF condition / ifnone flag so AddPathDelay
          // can route the entry under the LRM's conditional vs nonconditional
          // matching rules. A bare IOPATH leaves both fields at their defaults
          // (empty string, false) and dispatches as nonconditional.
          pd.condition = io.condition;
          pd.is_ifnone = io.is_ifnone;
          // §32.8 Table 32-4: extend the SDF rise/fall/turnoff triplet
          // into all twelve SystemVerilog transition slots before the
          // PathDelay lands on the manager. SdfIopath models exactly
          // three SDF delays per IOPATH so we always select the
          // three-value column. Slots [3..11] used to be left at zero,
          // which silently dropped to-z and X-state transition delays;
          // routing through ExpandSdfDelays applies the §32.8 rule and
          // populates them.
          {
            const auto expanded =
                ExpandSdfDelays({io.rise, io.fall, io.turnoff}, mtm);
            pd.delay_count = 12;
            for (int i = 0; i < 12; ++i) pd.delays[i] = expanded[i];
          }
          if (!io.extended_form) {
            // §32.6 sentence 3: an INCREMENT-mode IOPATH modifies the
            // matched path's existing delays additively rather than
            // overwriting them. Pulse limits stay where the prior
            // ABSOLUTE / PATHPULSE annotation left them, since the
            // INCREMENT description is restricted to the propagation
            // delays. Skip the default-reset of pulse limits in this
            // branch for the same reason.
            if (io.is_increment) {
              mgr.IncrementPathDelay(pd);
              break;
            }
            // §32.5 example 1 + §32.7 sentence 1: an ABSOLUTE IOPATH
            // annotation overwrites the path's pulse-filter limits.
            // Default reject and error are derived from the
            // SpecifyManager's pulse-limit invocation percentages
            // (defaulted to 100/100, which collapses to the inertial-
            // delay baseline). Computing the defaults from the
            // percentage settings is what §32.7 specifies for "the
            // default values annotated for pulse limits"; without it,
            // a model that opted into custom percentages would still
            // see 100%-of-delay limits on every SDF IOPATH installation.
            ApplyGlobalPulseLimits(pd, mgr.RejectPulseLimitPercent(),
                                    mgr.ErrorPulseLimitPercent());
            mgr.AddPathDelay(pd);
            break;
          }
          // §32.5 examples 2 and 3: the extended IOPATH form carries
          // per-direction reject and error slots that may be empty.
          // When every pulse-limit slot was empty the path's prior
          // reject and error survive the overwrite (example 2);
          // otherwise the supplied values install onto every transition
          // slot, with the simple-form default-reset filling in any
          // unsupplied slots (example 3, plus mixed-supply edge cases).
          const bool any_pulse_supplied =
              io.rise_reject_present || io.rise_error_present ||
              io.fall_reject_present || io.fall_error_present;
          if (!any_pulse_supplied) {
            mgr.AddPathDelay(pd, /*preserve_pulse_limits=*/true);
            break;
          }
          // §32.7 sentence 1: even when the extended IOPATH supplies
          // some pulse-limit slots, any unsupplied slots fall back to
          // the percentage-derived default rather than mirroring the
          // raw delay. This keeps the partial-supply path consistent
          // with the simple-form ABSOLUTE branch above so callers that
          // opted into custom percentages observe them everywhere SDF
          // delay annotation produces a default.
          ApplyGlobalPulseLimits(pd, mgr.RejectPulseLimitPercent(),
                                  mgr.ErrorPulseLimitPercent());
          if (io.rise_reject_present || io.fall_reject_present) {
            const SdfDelayValue& src_dv = io.rise_reject_present
                                              ? io.rise_reject
                                              : io.fall_reject;
            const uint64_t reject = SelectMtm(src_dv, mtm);
            for (int i = 0; i < 12; ++i) pd.reject_limit[i] = reject;
          }
          if (io.rise_error_present || io.fall_error_present) {
            const SdfDelayValue& src_dv = io.rise_error_present
                                              ? io.rise_error
                                              : io.fall_error;
            const uint64_t err = SelectMtm(src_dv, mtm);
            for (int i = 0; i < 12; ++i) pd.error_limit[i] = err;
          }
          mgr.AddPathDelay(pd);
          break;
        }
        case SdfDelayEntryKind::kPulseLimit: {
          const auto& pl = cell.pulse_limits[entry.index];
          // §32.4.1 Table 32-1 PATHPULSE / PATHPULSEPERCENT: route the parsed
          // entry through the manager helper that fans the limits across
          // all matching specify paths, regardless of their condition. The
          // percent/absolute distinction is preserved on the SdfPulseLimit
          // and dispatched inside the manager.
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
          // §32.4.4 + §32.8 Table 32-4: extend the SDF rise/(fall)
          // interconnect delays into all twelve SystemVerilog transition
          // slots. A purely-zero fall across min/typ/max is the SDF
          // single-value-input convention and selects Table 32-4's
          // one-value column; a supplied fall selects the two-value
          // column. Routing through the §32.8 helper replaces the
          // §30.5.1-based expansion the prior implementation used and
          // matches the IOPATH branch above on the same SDF value
          // mapping table.
          const bool fall_supplied = ic.fall.min_val != 0 ||
                                       ic.fall.typ_val != 0 ||
                                       ic.fall.max_val != 0;
          std::vector<SdfDelayValue> ic_vals;
          ic_vals.push_back(ic.rise);
          if (fall_supplied) ic_vals.push_back(ic.fall);
          const auto expanded = ExpandSdfDelays(ic_vals, mtm);
          for (int i = 0; i < 12; ++i) {
            delay.delays[i] = expanded[i];
            // §32.4.4: each of the twelve transition delays carries its
            // own reject and error pulse limit. Initialise both to the
            // matching delay so the default inertial-delay behaviour
            // applies — a pulse narrower than the propagation delay is
            // rejected — until a later mechanism revises the limits.
            delay.reject_limit[i] = expanded[i];
            delay.error_limit[i] = expanded[i];
          }
          // §32.6 sentence 3: INCREMENT-mode interconnect entries add
          // onto whatever the prior ABSOLUTE annotation installed for
          // the same (src, dst) pair. The PORT/NETDELAY load-only wipe
          // rule is intentionally not run for INCREMENT — modify
          // accumulates rather than wiping siblings.
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
      // §32.6 sentence 3 on the specparam category: an INCREMENT-mode
      // entry must add onto the matched specparam's running value rather
      // than overwriting it, paralleling the IOPATH/INTERCONNECT
      // INCREMENT routing above.
      if (sp.is_increment) {
        mgr.IncrementSpecparamValue(std::move(value));
      } else {
        mgr.SetSpecparamValue(std::move(value));
      }
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
  }
  return result;
}

// =============================================================================
// §32.9 $sdf_annotate argument helpers
// =============================================================================

bool ParseSdfMtmKeyword(std::string_view text, SdfMtmKeyword& out) {
  // Table 32-5 lists exactly these four spellings; case is fixed by
  // the table so no case folding is performed here.
  if (text == "MAXIMUM") { out = SdfMtmKeyword::kMaximum; return true; }
  if (text == "MINIMUM") { out = SdfMtmKeyword::kMinimum; return true; }
  if (text == "TYPICAL") { out = SdfMtmKeyword::kTypical; return true; }
  if (text == "TOOL_CONTROL") {
    out = SdfMtmKeyword::kToolControl;
    return true;
  }
  return false;
}

SdfMtm ResolveSdfMtm(SdfMtmKeyword keyword, SdfMtm tool_default) {
  // The named keywords each select a fixed slot of the SDF triplet;
  // TOOL_CONTROL hands back whatever the simulator's own delay-mode
  // option selected for this run.
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
  if (text == "FROM_MTM") { out = SdfScaleType::kFromMtm; return true; }
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

// Parse one real number from `text` starting at `pos`, advancing `pos`
// past the consumed characters. Returns true and writes the parsed
// value to `out`; returns false if no real number could be read.
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
  // §32.9 default "1.0:1.0:1.0": an empty argument resets every slot
  // to the LRM default rather than leaving the caller's prior values
  // in place, so a caller that reuses the same SdfScaleFactors across
  // calls observes the documented default.
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

// Round a non-negative real to the nearest tick for storage on
// SdfDelayValue's uint64_t slot. Negative inputs would never come
// from the LRM-defined math (every factor is non-negative and every
// SDF source value is non-negative), but the std::max guard keeps a
// downstream cast from wrapping if a caller ever supplies a
// pathological factor.
static uint64_t RoundToTicks(double scaled) {
  if (scaled <= 0.0) return 0;
  return static_cast<uint64_t>(std::floor(scaled + 0.5));
}

SdfDelayValue ApplySdfScaling(SdfDelayValue value, SdfScaleType type,
                              const SdfScaleFactors& factors) {
  // Pick the source value each output slot draws from. For FROM_MTM
  // the three slots stay independent; the three single-source forms
  // collapse all three source picks to one slot.
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
  // One line per individual annotation, prefixed with the cell's
  // type/instance pair so the reader can tie an entry back to a
  // specific SDF cell. Each line names the construct kind and the
  // timing data that was annotated — the typical-slot value or
  // limit — so the log is a per-annotation trail of timing data
  // rather than just a list of construct names. The exact format is
  // implementation-defined; §32.9 only requires that "an entry"
  // exists per annotation.
  for (const auto& cell : file.cells) {
    const std::string prefix = cell.cell_type + "/" + cell.instance + ": ";
    for (const auto& io : cell.iopaths) {
      out << prefix << "IOPATH " << io.src_port << " -> " << io.dst_port
          << " rise=" << io.rise.typ_val
          << " fall=" << io.fall.typ_val << '\n';
    }
    for (const auto& ic : cell.interconnects) {
      out << prefix << "INTERCONNECT " << ic.src_port << " -> " << ic.dst_port
          << " rise=" << ic.rise.typ_val
          << " fall=" << ic.fall.typ_val << '\n';
    }
    for (const auto& pl : cell.pulse_limits) {
      out << prefix << "PATHPULSE " << pl.src_port << " -> " << pl.dst_port
          << " reject=" << pl.reject.typ_val
          << " error=" << pl.error.typ_val << '\n';
    }
    for (const auto& tc : cell.timing_checks) {
      out << prefix << "TIMINGCHECK " << tc.data_port << " ref=" << tc.ref_port
          << " limit=" << tc.limit.typ_val << '\n';
    }
    for (const auto& sp : cell.specparams) {
      out << prefix << "SPECPARAM " << sp.name
          << " value=" << sp.value.typ_val << '\n';
    }
  }
  return true;
}

ResolvedSdfAnnotateArgs ResolveSdfAnnotateArgs(
    std::string_view explicit_mtm_spec,
    std::string_view explicit_scale_factors,
    std::string_view explicit_scale_type,
    const SdfAnnotateConfig& config) {
  ResolvedSdfAnnotateArgs out;

  // R14: prefer the explicit mtm_spec argument; fall back to the
  // config-file MTM_SPEC keyword when the explicit argument is
  // empty; fall back to TOOL_CONTROL (the LRM default) when both
  // layers are empty or unparseable. Each layer is consulted by
  // the same per-keyword parser so an unknown spelling at one
  // layer leaves the lower-precedence resolution intact.
  if (!config.mtm_spec.empty()) {
    ParseSdfMtmKeyword(config.mtm_spec, out.mtm);
  }
  if (!explicit_mtm_spec.empty()) {
    ParseSdfMtmKeyword(explicit_mtm_spec, out.mtm);
  }

  // R19: same precedence for scale_factors. ParseSdfScaleFactors
  // resets `out.factors` to 1.0:1.0:1.0 on an empty input, so
  // calling it unconditionally would discard the config-file
  // values when the explicit argument is omitted. Guard each call
  // on a non-empty source string instead, leaving the factors
  // untouched when the layer is silent.
  if (!config.scale_factors.empty()) {
    ParseSdfScaleFactors(config.scale_factors, out.factors);
  }
  if (!explicit_scale_factors.empty()) {
    ParseSdfScaleFactors(explicit_scale_factors, out.factors);
  }

  // R22: same precedence for scale_type, with the LRM default
  // (FROM_MTM) covered by ResolvedSdfAnnotateArgs's default
  // initialisation.
  if (!config.scale_type.empty()) {
    ParseSdfScaleType(config.scale_type, out.scale_type);
  }
  if (!explicit_scale_type.empty()) {
    ParseSdfScaleType(explicit_scale_type, out.scale_type);
  }

  return out;
}

}  // namespace delta
