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

static SdfSignalRef ParseSdfCondSignal(std::string_view& s) {
  SdfSignalRef ref;
  auto tokens = ParseSdfCondTokens(s);
  SkipWhitespace(s);
  if (!s.empty() && s[0] == '(') {
    ref.condition = JoinSdfCondTokens(tokens, tokens.size());
    Expect(s, SdfTokKind::kLParen);
    ReadSdfEdge(TakeSdfWord(s), ref);
    ref.port = std::string(TakeSdfWord(s));
    Expect(s, SdfTokKind::kRParen);
  } else if (!tokens.empty()) {
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
