#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>
#include <vector>

#include "preprocessor/protect_cli.h"

using namespace delta;

namespace {

ProtectCliOptions Parsed(std::initializer_list<const char*> args) {
  std::vector<const char*> argv(args);
  ProtectCliOptions opts;
  for (int i = 0; i < static_cast<int>(argv.size()); ++i) {
    TryParseProtectArg(argv[static_cast<size_t>(i)], i,
                       static_cast<int>(argv.size()), argv.data(), opts);
  }
  return opts;
}

struct ProtectArgParse {
  bool recognized = false;
  ProtectCliOptions opts;
};

ProtectArgParse ParsedArg(std::initializer_list<const char*> args) {
  std::vector<const char*> argv(args);
  ProtectArgParse parse;
  int i = 0;
  parse.recognized = TryParseProtectArg(
      argv[0], i, static_cast<int>(argv.size()), argv.data(), parse.opts);
  return parse;
}

TEST(ProtectCliParsing, EncryptOptionIsRecorded) {
  EXPECT_TRUE(Parsed({"--encrypt"}).encrypt);
}

TEST(ProtectCliParsing, EncryptIsOffWhenUnasked) {
  EXPECT_FALSE(Parsed({"--protect-key", "acme-key"}).encrypt);
}

TEST(ProtectCliParsing, ExchangeKeyIsRecorded) {
  EXPECT_EQ(Parsed({"--protect-key", "acme-key"}).exchange_key, "acme-key");
}

TEST(ProtectCliParsing, NamedKeyIsRecordedUnderItsOwnerAndName) {
  auto opts = Parsed({"--protect-named-key", "acme:rsa-2048=acme-key"});
  EXPECT_EQ(opts.keys.KeyFor("acme", "rsa-2048"), "acme-key");
}

TEST(ProtectCliParsing, ANamedKeyLeavesTheExchangeKeyAlone) {
  auto opts = Parsed({"--protect-key", "acme-key", "--protect-named-key",
                      "widget:rsa-2048=widget-key"});
  EXPECT_EQ(opts.exchange_key, "acme-key");
}

TEST(ProtectCliParsing, ExchangeKeyWithNoValueIsRefusedRatherThanUnrecognized) {
  auto parse = ParsedArg({"--protect-key"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

TEST(ProtectCliParsing, NamedKeyWithNoValueIsRefusedRatherThanUnrecognized) {
  auto parse = ParsedArg({"--protect-named-key"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

TEST(ProtectCliParsing, NamedKeyWithNoColonIsRefused) {
  auto parse = ParsedArg({"--protect-named-key", "rsa-2048=acme-key"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

TEST(ProtectCliParsing, NamedKeyWithNoEqualsIsRefused) {
  auto parse = ParsedArg({"--protect-named-key", "acme:rsa-2048"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

TEST(ProtectCliParsing, NamedKeyWithAnEmptyOwnerIsRefused) {
  auto parse = ParsedArg({"--protect-named-key", ":rsa-2048=acme-key"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

TEST(ProtectCliParsing, NamedKeyWithAnEmptyNameOrKeyIsRefused) {
  for (const char* value : {"acme:=acme-key", "acme:rsa-2048="}) {
    auto parse = ParsedArg({"--protect-named-key", value});
    EXPECT_TRUE(parse.recognized) << value;
    EXPECT_TRUE(parse.opts.rejected_argument) << value;
    EXPECT_FALSE(parse.opts.keys.KnowsOwner("acme")) << value;
  }
}

TEST(ProtectCliParsing, AnEmptyExchangeKeyIsRefused) {
  auto parse = ParsedArg({"--protect-key", ""});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
  EXPECT_TRUE(parse.opts.exchange_key.empty());
}

TEST(ProtectCliParsing, NamedKeyWithoutAnOwnerIsRefused) {
  auto opts = Parsed({"--protect-named-key", "rsa-2048=acme-key"});
  EXPECT_FALSE(opts.keys.KnowsOwner("rsa-2048"));
}

TEST(ProtectCliParsing, ExchangeKeyWithAValueSetsNoRejectedArgument) {
  auto parse = ParsedArg({"--protect-key", "acme-key"});
  EXPECT_EQ(parse.opts.exchange_key, "acme-key");
  EXPECT_FALSE(parse.opts.rejected_argument);
}

TEST(ProtectCliParsing, NamedKeyWithAWellFormedValueSetsNoRejectedArgument) {
  auto parse = ParsedArg({"--protect-named-key", "acme:rsa-2048=acme-key"});
  EXPECT_EQ(parse.opts.keys.KeyFor("acme", "rsa-2048"), "acme-key");
  EXPECT_FALSE(parse.opts.rejected_argument);
}

TEST(ProtectCliParsing, EncryptSetsNoRejectedArgument) {
  auto parse = ParsedArg({"--encrypt"});
  EXPECT_TRUE(parse.opts.encrypt);
  EXPECT_FALSE(parse.opts.rejected_argument);
}

TEST(ProtectCliParsing, AnUnrelatedArgumentIsNotConsumed) {
  const char* argv[] = {"--lint-only"};
  int i = 0;
  ProtectCliOptions opts;
  EXPECT_FALSE(TryParseProtectArg(argv[0], i, 1, argv, opts));
}

}  // namespace
