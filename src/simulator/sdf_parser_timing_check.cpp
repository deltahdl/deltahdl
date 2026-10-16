// §32.4.2 (printed page 926): the entries of an SDF TIMINGCHECK section, each
// a check keyword and the signals, edges, conditions and limits Table 32-2
// maps onto a SystemVerilog timing check. Split out of
// src/simulator/sdf_parser.cpp, which reads the section itself and hands each
// entry here.

#include <cctype>
#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_specify.h"
#include "simulator/sdf_parser.h"
#include "simulator/sdf_parser_internal.h"

namespace delta {

// Maps a TIMINGCHECK entry keyword to the check it annotates. Returns false for
// a keyword this annotator does not recognize; the caller decides what to do
// with it rather than falling back on an arbitrary check type.
bool MapCheckType(std::string_view name, SdfCheckType& out) {
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
  std::vector<std::pair<char, char>> edge_descriptors;

  std::string condition;
};

// §32.4.2: the edge an SDF signal was written with -- posedge, negedge, or one
// of the transitions 01, 10, 0z, z1, 1z and z0, each of which is §31.5's edge
// descriptor of that one transition, z read as the x §31.5 handles it as.
// Anything else leaves the edge unknown.
// The next word of `s`, up to white space or a parenthesis, taken whole: an
// edge such as 0z, which the token reader splits into a number and a name, or
// a port written with a range select, d[3:2], which it splits at the colon.
static std::string_view TakeSdfWord(std::string_view& s) {
  SkipWhitespace(s);
  std::size_t len = 0;
  while (len < s.size() && s[len] != '(' && s[len] != ')' &&
         std::isspace(static_cast<unsigned char>(s[len])) == 0) {
    ++len;
  }
  const std::string_view kWord = s.substr(0, len);
  s.remove_prefix(len);
  return kWord;
}

static void ReadSdfEdge(std::string_view text, SdfSignalRef& ref) {
  if (text == "posedge") {
    ref.edge = SpecifyEdge::kPosedge;
    return;
  }
  if (text == "negedge") {
    ref.edge = SpecifyEdge::kNegedge;
    return;
  }
  static constexpr std::string_view kTransitions[] = {"01", "10", "0z",
                                                      "z1", "1z", "z0"};
  for (const std::string_view kTransition : kTransitions) {
    if (text != kTransition) continue;
    const auto kLevel = [](char c) { return c == 'z' ? 'x' : c; };
    ref.edge = SpecifyEdge::kEdge;
    ref.edge_descriptors = {{kLevel(text[0]), kLevel(text[1])}};
    return;
  }
}

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
    ReadSdfEdge(TakeSdfWord(s), ref);
    ref.port = std::string(TakeSdfWord(s));
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
    const std::string_view kFirst = TakeSdfWord(s);
    if (kFirst == "COND") return ParseSdfCondSignal(s);
    ReadSdfEdge(kFirst, ref);
    ref.port = std::string(TakeSdfWord(s));
    Expect(s, SdfTokKind::kRParen);
  } else {
    ref.port = std::string(TakeSdfWord(s));
  }
  return ref;
}

// §32.4.2 with IEEE 1497: SETUP, HOLD and SETUPHOLD write the data signal
// first and the reference signal second; every other two-signal check --
// RECOVERY, REMOVAL, RECREM, SKEW, BIDIRECTSKEW and NOCHANGE -- writes the
// reference signal first, as the SystemVerilog check it annotates does.
// Reads the second signal of `tc`'s check, whose first is `first`, and
// records the two as the check's reference and data events.
static void ReadSignalPair(std::string_view& s, SdfSignalRef first,
                           SdfTimingCheck& tc) {
  auto second = ParseSdfSignal(s);
  const bool kDataFirst = (tc.check_type == SdfCheckType::kSetup ||
                           tc.check_type == SdfCheckType::kHold ||
                           tc.check_type == SdfCheckType::kSetuphold);
  SdfSignalRef& data = kDataFirst ? first : second;
  SdfSignalRef& ref = kDataFirst ? second : first;
  tc.data_port = data.port;
  tc.data_edge = data.edge;
  tc.data_edge_descriptors = data.edge_descriptors;
  tc.ref_port = ref.port;
  tc.ref_edge = ref.edge;
  tc.ref_edge_descriptors = ref.edge_descriptors;

  // §32.4.2: either signal of a timing check may carry a condition, and a
  // condition the file supplies has to match the declared check's condition
  // on that same signal -- dropping one would turn a conditioned check into
  // an unconditioned one, which matches every corresponding declaration
  // instead of only the one it names -- so the two are kept apart.
  tc.ref_condition = ref.condition;
  tc.data_condition = data.condition;
  tc.condition = ref.condition.empty() ? std::move(data.condition)
                                       : std::move(ref.condition);
}

SdfTimingCheck ParseOneTc(std::string_view& s, SdfCheckType type) {
  SdfTimingCheck tc;
  tc.check_type = type;

  const bool kSingleSignal =
      (type == SdfCheckType::kWidth || type == SdfCheckType::kPeriod);
  auto first = ParseSdfSignal(s);
  if (kSingleSignal) {
    tc.ref_port = first.port;
    tc.ref_edge = first.edge;
    tc.ref_edge_descriptors = first.edge_descriptors;

    tc.ref_condition = first.condition;
    tc.condition = std::move(first.condition);
  } else {
    ReadSignalPair(s, std::move(first), tc);
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
  // §32.3: a construct written after the values, an SCOND or a CCOND, is read
  // through to its own closing parenthesis, so the check's own one still
  // closes the check and the entries after it are read in step.
  SkipWhitespace(s);
  while (!s.empty() && s[0] == '(') {
    Expect(s, SdfTokKind::kLParen);
    if (tc.trailing_construct.empty()) {
      tc.trailing_construct = std::string(NextSdfToken(s).text);
    }
    SkipSdfParen(s);
    SkipWhitespace(s);
  }
  Expect(s, SdfTokKind::kRParen);
  return tc;
}

}  // namespace delta
