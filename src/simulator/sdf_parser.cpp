

#include "simulator/sdf_parser.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <string>
#include <vector>

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

// Fills a triple (min:typ:max) into `dv` given an already-parsed leading
// numeric token `first`. All three fields default to `first`; if a ':' follows
// the leading value, the optional typ and max values override the defaults.
static void ParseSdfDelayTypMax(std::string_view& s, const SdfToken& first,
                                SdfDelayValue& dv) {
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

static SdfDelayValue ParseDelayVal(std::string_view& s) {
  SdfDelayValue dv;

  if (!Expect(s, SdfTokKind::kLParen)) return dv;
  auto first = NextSdfToken(s);
  if (first.kind == SdfTokKind::kNumber) {
    ParseSdfDelayTypMax(s, first, dv);
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

// Collects the tokens making up a COND condition expression. It ends at the '('
// that opens a parenthesized construct or at the ')' closing the COND, neither
// of which is consumed -- what follows the expression is the caller's to read,
// because only the caller knows whether a port name comes next.
static std::vector<std::string> ParseSdfCondTokens(std::string_view& s) {
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

// Renders the first `count` collected tokens back as condition text, spaced the
// way SpecifyConditionText spaces the SystemVerilog side it is compared
// against.
static std::string JoinSdfCondTokens(const std::vector<std::string>& tokens,
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
  auto first = NextSdfToken(s);
  if (first.kind == SdfTokKind::kNumber) {
    *present = true;
    ParseSdfDelayTypMax(s, first, dv);
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

// Optionally consumes a leading (RETAIN ...) sub-expression. If the
// parenthesized form is not a RETAIN, the input is restored to its original
// position.
//
// §32.3: a retain spec states how long an output holds its former value after
// an input changes. That is propagation timing for the very path being read,
// not information from outside the simulator's concern, and SystemVerilog has
// no construct to hold it -- so it is data the annotator understands and still
// cannot place, and it is reported. The surrounding IOPATH is unaffected: its
// own delays are annotated as usual, and only the part that found no home is
// warned about.
static void SkipOptionalIopathRetain(std::string_view& s, SdfFile& file) {
  SkipWhitespace(s);
  if (s.size() >= 7 && s[0] == '(') {
    auto save = s;
    Expect(s, SdfTokKind::kLParen);
    auto peek = NextSdfToken(s);
    if (peek.text == "RETAIN") {
      SkipSdfParen(s);
      file.unannotatable.emplace_back("RETAIN");
    } else {
      s = save;
    }
  }
}

static void ApplyRiseDirection(const ExtendedIopathDir& dir, SdfIopath& io) {
  if (dir.delay_present) io.rise = dir.delay;
  io.rise_delay_present = dir.delay_present;
  io.rise_reject = dir.reject;
  io.rise_reject_present = dir.reject_present;
  io.rise_error = dir.error;
  io.rise_error_present = dir.error_present;
}

static void ApplyFallDirection(const ExtendedIopathDir& dir, SdfIopath& io) {
  if (dir.delay_present) io.fall = dir.delay;
  io.fall_delay_present = dir.delay_present;
  io.fall_reject = dir.reject;
  io.fall_reject_present = dir.reject_present;
  io.fall_error = dir.error;
  io.fall_error_present = dir.error_present;
}

// Parses the extended (parenthesized-direction) form of an IOPATH delay list:
// up to three directions for rise, fall, and turnoff.
static void ParseExtendedIopathDelays(std::string_view& s, SdfIopath& io) {
  ApplyRiseDirection(ParseExtendedDirection(s), io);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    ApplyFallDirection(ParseExtendedDirection(s), io);
  }
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    auto turnoff_dir = ParseExtendedDirection(s);

    if (turnoff_dir.delay_present) io.turnoff = turnoff_dir.delay;
  }
}

// Parses the simple form of an IOPATH delay list: bare rise, fall, and turnoff
// delay triples.
static void ParseSimpleIopathDelays(std::string_view& s, SdfIopath& io) {
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

static SdfIopath ParseIopath(std::string_view& s, SdfFile& file) {
  SdfIopath io;
  io.src_port = ParseSdfPort(s);
  io.dst_port = ParseSdfPort(s);

  SkipOptionalIopathRetain(s, file);

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

// Maps a TIMINGCHECK entry keyword to the check it annotates. Returns false for
// a keyword this annotator does not recognize; the caller decides what to do
// with it rather than falling back on an arbitrary check type.
static bool MapCheckType(std::string_view name, SdfCheckType& out) {
  if (name == "SETUP") {
    out = SdfCheckType::kSetup;
  } else if (name == "HOLD") {
    out = SdfCheckType::kHold;
  } else if (name == "SETUPHOLD") {
    out = SdfCheckType::kSetuphold;
  } else if (name == "RECOVERY") {
    out = SdfCheckType::kRecovery;
  } else if (name == "REMOVAL") {
    out = SdfCheckType::kRemoval;
  } else if (name == "RECREM") {
    out = SdfCheckType::kRecrem;
  } else if (name == "WIDTH") {
    out = SdfCheckType::kWidth;
  } else if (name == "PERIOD") {
    out = SdfCheckType::kPeriod;
  } else if (name == "SKEW") {
    out = SdfCheckType::kSkew;
  } else if (name == "BIDIRECTSKEW") {
    out = SdfCheckType::kBidirectskew;
  } else if (name == "NOCHANGE") {
    out = SdfCheckType::kNochange;
  } else {
    return false;
  }
  return true;
}

struct SdfSignalRef {
  std::string port;
  SpecifyEdge edge = SpecifyEdge::kNone;

  std::string condition;
};

// Parses the condition text and the (optionally edge-qualified) port that
// follow a leading COND keyword inside a signal reference. The opening '(' of
// the COND form has already been consumed.
static SdfSignalRef ParseSdfCondSignal(std::string_view& s) {
  SdfSignalRef ref;
  auto tokens = ParseSdfCondTokens(s);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    // The port comes parenthesized with its edge, so every token collected so
    // far belongs to the condition.
    ref.condition = JoinSdfCondTokens(tokens, tokens.size());
    Expect(s, SdfTokKind::kLParen);
    auto edge_tok = NextSdfToken(s);
    if (edge_tok.text == "posedge")
      ref.edge = SpecifyEdge::kPosedge;
    else if (edge_tok.text == "negedge")
      ref.edge = SpecifyEdge::kNegedge;
    auto port_tok = NextSdfToken(s);
    ref.port = std::string(port_tok.text);
    Expect(s, SdfTokKind::kRParen);
  } else if (!tokens.empty()) {
    // §32.4.2: a signal may carry a condition without carrying an edge, and
    // then the bare port name closes the COND. It is the last thing collected;
    // everything before it is the condition. Reading it as part of the
    // condition instead would leave the check naming no signal at all.
    ref.port = tokens.back();
    ref.condition = JoinSdfCondTokens(tokens, tokens.size() - 1);
  }
  Expect(s, SdfTokKind::kRParen);
  return ref;
}

static SdfSignalRef ParseSdfSignal(std::string_view& s) {
  SdfSignalRef ref;
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    Expect(s, SdfTokKind::kLParen);
    auto first_tok = NextSdfToken(s);

    if (first_tok.text == "COND") {
      return ParseSdfCondSignal(s);
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

  const bool kSingleSignal =
      (type == SdfCheckType::kWidth || type == SdfCheckType::kPeriod);
  auto first = ParseSdfSignal(s);
  if (kSingleSignal) {
    tc.ref_port = first.port;
    tc.ref_edge = first.edge;

    tc.condition = std::move(first.condition);
  } else {
    tc.data_port = first.port;
    tc.data_edge = first.edge;
    auto ref = ParseSdfSignal(s);
    tc.ref_port = ref.port;
    tc.ref_edge = ref.edge;

    // §32.4.2: either signal of a timing check may carry a condition, and a
    // condition the file supplies has to take part in matching -- dropping one
    // would turn a conditioned check into an unconditioned one, which matches
    // every corresponding declaration instead of only the one it names. The
    // reference signal's condition identifies the check where it has one; a
    // condition carried only by the data signal identifies it instead, which is
    // the same precedence the SystemVerilog side of the match uses.
    tc.condition = ref.condition.empty() ? std::move(first.condition)
                                         : std::move(ref.condition);
  }
  tc.limit = ParseDelayVal(s);

  const bool kTwoValue =
      (type == SdfCheckType::kSetuphold || type == SdfCheckType::kRecrem ||
       type == SdfCheckType::kBidirectskew || type == SdfCheckType::kNochange);
  if (kTwoValue) {
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

// §32.4.1 Table 32-1: a DEVICE entry. The operand naming the instance or output
// it applies to is optional -- an entry that opens straight into a delay value
// carries none -- and up to three delay values follow, read the same way an
// IOPATH's are.
static SdfDevice ParseDeviceEntry(std::string_view& s) {
  SdfDevice dev;
  dev.port_instance = ParseSdfPort(s);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    dev.rise = ParseDelayVal(s);
  }
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    dev.fall = ParseDelayVal(s);
  }
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    dev.turnoff = ParseDelayVal(s);
  }
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

static void RecordDelayEntry(SdfCell& cell, SdfDelayEntryKind kind,
                             size_t index) {
  SdfDelayEntryRef ref;
  ref.kind = kind;
  ref.index = static_cast<uint32_t>(index);
  cell.delay_entry_order.push_back(ref);
}

// Appends an already-parsed iopath to the cell and records its delay-entry
// order slot.
static void AddIopathToCell(SdfCell& cell, const SdfIopath& io) {
  cell.iopaths.push_back(io);
  RecordDelayEntry(cell, SdfDelayEntryKind::kIopath, cell.iopaths.size() - 1);
}

// Appends an already-parsed interconnect to the cell and records its
// delay-entry order slot.
static void AddInterconnectToCell(SdfCell& cell, SdfInterconnect&& ic) {
  cell.interconnects.push_back(std::move(ic));
  RecordDelayEntry(cell, SdfDelayEntryKind::kInterconnect,
                   cell.interconnects.size() - 1);
}

// Parses a load-only interconnect (PORT/NETDELAY) of the given kind and adds it
// to the cell.
static void ParseAndAddLoadOnlyInterconnect(std::string_view& s, SdfCell& cell,
                                            SdfInterconnectKind kind,
                                            bool increment) {
  auto ic = ParseLoadOnlyInterconnect(s, kind);
  ic.is_increment = increment;
  AddInterconnectToCell(cell, std::move(ic));
}

// Handles a (COND ...) delay-section entry: a conditioned IOPATH is recorded,
// any other inner construct is skipped and reported unannotatable.
static void ParseCondDelayEntry(std::string_view& s, SdfCell& cell,
                                SdfFile& file, bool increment) {
  std::string cond = ParseSdfConditionText(s);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    Expect(s, SdfTokKind::kLParen);
    auto inner = NextSdfToken(s);
    if (inner.text == "IOPATH") {
      auto io = ParseIopath(s, file);
      io.is_increment = increment;
      io.condition = std::move(cond);
      AddIopathToCell(cell, io);
      Expect(s, SdfTokKind::kRParen);
      return;
    }

    SkipSdfParen(s);
  }
  file.unannotatable.emplace_back("COND");

  SkipWhitespace(s);
  if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
}

// Handles a (CONDELSE ...) delay-section entry: an ifnone IOPATH is recorded,
// any other inner construct is skipped and reported unannotatable.
static void ParseCondElseDelayEntry(std::string_view& s, SdfCell& cell,
                                    SdfFile& file, bool increment) {
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    Expect(s, SdfTokKind::kLParen);
    auto inner = NextSdfToken(s);
    if (inner.text == "IOPATH") {
      auto io = ParseIopath(s, file);
      io.is_increment = increment;
      io.is_ifnone = true;
      AddIopathToCell(cell, io);
      Expect(s, SdfTokKind::kRParen);
      return;
    }
    SkipSdfParen(s);
  }
  file.unannotatable.emplace_back("CONDELSE");
  SkipWhitespace(s);
  if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
}

// Handles a (PATHPULSE ...) / (PATHPULSEPERCENT ...) delay-section entry:
// parses the pulse limit, records the percent flag, and appends it to the cell.
static void ParsePulseLimitDelayEntry(std::string_view& s, SdfCell& cell,
                                      bool is_percent) {
  auto pl = ParsePulseLimit(s);
  pl.is_percent = is_percent;
  cell.pulse_limits.push_back(pl);
  RecordDelayEntry(cell, SdfDelayEntryKind::kPulseLimit,
                   cell.pulse_limits.size() - 1);
}

// Handles a (INTERCONNECT ...) delay-section entry.
static void ParseInterconnectDelayEntry(std::string_view& s, SdfCell& cell,
                                        bool increment) {
  auto ic = ParseInterconnectEntry(s);
  ic.is_increment = increment;
  AddInterconnectToCell(cell, std::move(ic));
}

// Handles a (DEVICE ...) delay-section entry.
static void ParseDeviceDelayEntry(std::string_view& s, SdfCell& cell,
                                  bool increment) {
  auto dev = ParseDeviceEntry(s);
  dev.is_increment = increment;
  cell.devices.push_back(std::move(dev));
  RecordDelayEntry(cell, SdfDelayEntryKind::kDevice, cell.devices.size() - 1);
}

// Handles a (IOPATH ...) delay-section entry.
static void ParseIopathDelayEntry(std::string_view& s, SdfCell& cell,
                                  SdfFile& file, bool increment) {
  auto io = ParseIopath(s, file);
  io.is_increment = increment;
  AddIopathToCell(cell, io);
}

// Dispatches a single already-opened delay-section entry (the leading '(' and
// keyword have been consumed) to the handler for its keyword.
static void HandleDelayEntry(std::string_view& s, SdfCell& cell, SdfFile& file,
                             const SdfToken& kw, bool increment) {
  if (kw.text == "PATHPULSE" || kw.text == "PATHPULSEPERCENT") {
    ParsePulseLimitDelayEntry(s, cell, kw.text == "PATHPULSEPERCENT");
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

// Parses the body of a DELAY section, whose leading keyword selects whether the
// delays it lists replace or add to the ones already in place.
//
// §32.3: a leading keyword this annotator does not recognize makes the whole
// section data it is unable to annotate, so it is reported and skipped. Reading
// its contents as an absolute delay list anyway would push delays onto module
// paths under a mode the SDF file never asked for.
static void ParseDelaySpec(std::string_view& s, SdfCell& cell, SdfFile& file) {
  Expect(s, SdfTokKind::kLParen);
  auto mode = NextSdfToken(s);
  if (mode.text != "ABSOLUTE" && mode.text != "INCREMENT") {
    file.unannotatable.emplace_back(mode.text);
    SkipSdfParen(s);
    SkipWhitespace(s);
    if (!s.empty() && s[0] == ')') Expect(s, SdfTokKind::kRParen);
    return;
  }
  ParseDelaySection(s, cell, file, mode.text == "INCREMENT");
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
    // §32.3: an entry of a TIMINGCHECK section is timing data by construction,
    // so one this annotator does not recognize is data it is unable to
    // annotate and has to be reported. Guessing a check type for it instead
    // would overwrite a timing check constraint the SDF file never provided a
    // value for, which the same subclause forbids.
    if (!MapCheckType(kw.text, ct)) {
      file.unannotatable.emplace_back(kw.text);
      SkipSdfParen(s);
      continue;
    }
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

}  // namespace delta
