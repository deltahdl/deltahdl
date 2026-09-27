// §32.4.2 (printed page 926): the entries of an SDF TIMINGCHECK section, each
// a check keyword and the signals, edges, conditions and limits Table 32-2
// maps onto a SystemVerilog timing check. Split out of
// src/simulator/sdf_parser.cpp, which reads the section itself and hands each
// entry here.

#include <string>
#include <string_view>
#include <utility>

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

SdfTimingCheck ParseOneTc(std::string_view& s, SdfCheckType type) {
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

}  // namespace delta
