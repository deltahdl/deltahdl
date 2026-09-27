

#include "simulator/sdf_parser.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
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

// A number, together with the leading minus sign a value that lowers what it
// annotates is written with. The token's text keeps the sign, so a caller
// rendering the token back as source writes what the file wrote, while the
// value and the sign are reported apart.
static SdfToken LexNumber(std::string_view& s) {
  const size_t kFirstDigit = (!s.empty() && s[0] == '-') ? 1 : 0;
  size_t len = kFirstDigit;
  while (len < s.size() && (std::isdigit(s[len]) != 0)) ++len;
  SdfToken tok;
  tok.kind = SdfTokKind::kNumber;
  tok.text = s.substr(0, len);
  tok.num_val = 0;
  tok.is_negative = kFirstDigit == 1;
  for (size_t i = kFirstDigit; i < len; ++i) {
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

SdfToken NextSdfToken(std::string_view& s) {
  SkipWhitespace(s);
  if (s.empty()) return {SdfTokKind::kEof, {}, 0};
  char ch = s[0];
  if (ch == '(') return MakeSingleChar(s, SdfTokKind::kLParen);
  if (ch == ')') return MakeSingleChar(s, SdfTokKind::kRParen);
  if (ch == ':') return MakeSingleChar(s, SdfTokKind::kColon);
  if (ch == '"') return LexString(s);
  // A minus sign belongs to the number it introduces; standing on its own it is
  // ordinary text, an operator in a condition expression among other things.
  const bool kSignedNumber =
      ch == '-' && s.size() > 1 && (std::isdigit(s[1]) != 0);
  if ((std::isdigit(ch) != 0) || kSignedNumber) return LexNumber(s);
  return LexIdent(s);
}

bool Expect(std::string_view& s, SdfTokKind kind) {
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
  dv.min_negative = first.is_negative;
  dv.typ_negative = first.is_negative;
  dv.max_negative = first.is_negative;

  SkipWhitespace(s);
  if (!s.empty() && s[0] == ':') {
    Expect(s, SdfTokKind::kColon);
    auto typ = NextSdfToken(s);
    if (typ.kind == SdfTokKind::kNumber) {
      dv.typ_val = typ.num_val;
      dv.typ_negative = typ.is_negative;
    }
    Expect(s, SdfTokKind::kColon);
    auto max_tok = NextSdfToken(s);
    if (max_tok.kind == SdfTokKind::kNumber) {
      dv.max_val = max_tok.num_val;
      dv.max_negative = max_tok.is_negative;
    }
  }
}

SdfDelayValue ParseDelayVal(std::string_view& s) {
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
  std::string port(tok.text);
  // §32.4.1: a port may be written with a part-select, `b[3:2]`, whose colon
  // the lexer takes as a token of its own; the rest of the select, up to its
  // closing bracket, is joined back onto the name.
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

// Renders the first `count` collected tokens back as condition text, one space
// between each.
//
// That is not how SpecifyConditionText spaces the SystemVerilog side, and no
// join rule could be: NextSdfToken above lexes `:` as a token of its own, so
// `mode[3:2]` arrives here as three tokens and `c ? a : b` as five, and one
// spacing cannot serve both. SpecifyConditionsMatch in
// simulator/specify_condition_text.cpp is what reconciles the two, comparing
// them with whitespace ignored.
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
// up to three directions for rise, fall, and turnoff. §32.8: each direction
// read contributes one delay value to the list, whether or not it wrote a
// delay, so a direction that held its delay still counts towards how many
// values the entry supplied.
static void ParseExtendedIopathDelays(std::string_view& s, SdfIopath& io) {
  ApplyRiseDirection(ParseExtendedDirection(s), io);
  io.values.push_back(io.rise);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    ApplyFallDirection(ParseExtendedDirection(s), io);
    io.values.push_back(io.fall);
  }
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    auto turnoff_dir = ParseExtendedDirection(s);

    if (turnoff_dir.delay_present) io.turnoff = turnoff_dir.delay;
    io.values.push_back(io.turnoff);
  }
}

// §32.8: parses the simple form of an IOPATH delay list. A module path carries
// twelve state transition delays and an entry fills them in from a listed one,
// two, three, six or twelve values, so the whole list is read rather than only
// a rise/fall/turnoff triple.
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

// §32.4.1: an IOPATH's source port, which may be written with an edge,
// `(posedge clk)`; the port's name, with the edge recorded on `io`. posedge
// and negedge are the edges a module path declares (§30.4.2); any other edge
// the SDF file writes leaves the source's edge unknown. Read as a bare port, a
// parenthesized source read as no name, and the rest of the entry was
// reported token by token as constructs that could not be annotated.
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

static SdfIopath ParseIopath(std::string_view& s, SdfFile& file) {
  SdfIopath io;
  io.src_port = ParseIopathSource(s, io);
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

// §32.4.4: reads the delay list of an interconnect entry. An interconnect delay
// has twelve transition delays and is filled in from a listed one, two, three,
// six or twelve values the same way a module path delay is, so the whole list
// is read rather than only the first two values.
static void ParseInterconnectDelayList(std::string_view& s,
                                       SdfInterconnect& ic) {
  while (ic.values.size() < 12) {
    SkipWhitespace(s);
    if (s.empty() || s[0] != '(') break;
    ic.values.push_back(ParseDelayVal(s));
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

// §32.4.1 Table 32-1: a DEVICE entry. The operand naming the instance or output
// it applies to is optional -- an entry that opens straight into a delay value
// carries none. §32.8: the delay values that follow are read as a whole list
// rather than as a fixed rise/fall/turnoff triple, because a DEVICE delay may
// land on a specify path, which carries twelve state transition delays, as
// readily as on a gate primitive, which carries three -- and how many values
// were written is what decides both mappings.
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

// §32.5: notes where in the cell's run of constructs this one occurred, so
// annotation can later replay them in exactly that order.
static void RecordCellEntry(SdfCell& cell, SdfCellEntryKind kind,
                            size_t index) {
  SdfCellEntryRef ref;
  ref.kind = kind;
  ref.index = static_cast<uint32_t>(index);
  cell.entry_order.push_back(ref);
}

// Appends an already-parsed iopath to the cell and records its delay-entry
// order slot; one whose source edge names no edge a module path declares is
// reported instead.
static void AddIopathToCell(SdfCell& cell, SdfFile& file, const SdfIopath& io) {
  if (!io.src_edge_known) {
    file.unannotatable.emplace_back("IOPATH");
    return;
  }
  cell.iopaths.push_back(io);
  RecordCellEntry(cell, SdfCellEntryKind::kIopath, cell.iopaths.size() - 1);
}

// Appends an already-parsed interconnect to the cell and records its
// delay-entry order slot.
static void AddInterconnectToCell(SdfCell& cell, SdfInterconnect&& ic) {
  cell.interconnects.push_back(std::move(ic));
  RecordCellEntry(cell, SdfCellEntryKind::kInterconnect,
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

// Handles a (PATHPULSE ...) / (PATHPULSEPERCENT ...) delay-section entry:
// parses the pulse limit, records the percent flag, and appends it to the cell.
static void ParsePulseLimitDelayEntry(std::string_view& s, SdfCell& cell,
                                      bool is_percent, bool increment) {
  auto pl = ParsePulseLimit(s);
  pl.is_percent = is_percent;
  pl.is_increment = increment;
  cell.pulse_limits.push_back(pl);
  RecordCellEntry(cell, SdfCellEntryKind::kPulseLimit,
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
  RecordCellEntry(cell, SdfCellEntryKind::kDevice, cell.devices.size() - 1);
}

// Handles a (IOPATH ...) delay-section entry.
static void ParseIopathDelayEntry(std::string_view& s, SdfCell& cell,
                                  SdfFile& file, bool increment) {
  auto io = ParseIopath(s, file);
  io.is_increment = increment;
  AddIopathToCell(cell, file, io);
}

// Dispatches a single already-opened delay-section entry (the leading '(' and
// keyword have been consumed) to the handler for its keyword.
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

// Parses the body of a DELAY section: one or more deltypes, each of whose
// leading keyword selects whether the delays it lists replace or add to the
// ones already in place. §32.5 (printed pages 929-930) has them annotate in
// the order written, so an INCREMENT after an ABSOLUTE in one section adds to
// it; read as a section of one deltype, the second was taken for the section's
// end and dropped.
//
// §32.3: a leading keyword this annotator does not recognize makes that deltype
// data it is unable to annotate, so it is reported and skipped. Reading its
// contents as an absolute delay list anyway would push delays onto module
// paths under a mode the SDF file never asked for.
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
  }
  return dv;
}

// One lbl_type of a LABEL section, its leading `(` already read: the mode, and
// the specparam values it lists in that mode, through its closing `)`. A mode
// this annotator does not know is reported and skipped.
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

// A LABEL section holds one or more lbl_types, as a DELAY section holds one or
// more deltypes, and §32.5 annotates them in the order written; read as a
// section of one, a second was taken for the section's end.
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
      // SDF writes a cell at the level the annotation runs at with its path
      // left out, `(INSTANCE)`, which SdfCellPrefixInRegion reads as the region
      // itself; read as a name, the closing parenthesis became the path and
      // the cell's next construct was taken for the close.
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
