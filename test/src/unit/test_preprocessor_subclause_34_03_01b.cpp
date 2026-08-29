// §34.3.1's encrypting mode as the command line asks for it: which option turns
// the mode on, which option names the single key every region is encrypted
// under, and which option names a key by the entity that owns it and the name
// it was given.
//
// Every case here calls TryParseProtectArg (preprocessor/protect_cli.h) with a
// command line and reads the ProtectCliOptions field the option is supposed to
// reach. No case preprocesses a source text.
//
// A refusal here is asserted through TryParseProtectArg's return value and
// ProtectCliOptions::rejected_argument together. The return value says the
// argument was one of these options; the field says the option refused the
// value written after it. CLAUDE.md otherwise has a test naming the report
// through ReportedError, which applies to a rule the program reports through
// common/diagnostic.h; TryParseProtectArg writes to std::cerr and returns a
// bool instead, so there is no diagnostic for a case to name.
//
// Issue #3427 is why a refused value is asserted as that pair rather than as
// either half. TryParseProtectArg matched `arg == "--protect-key" && i + 1 <
// argc`, so --protect-key written last with its value left off was answered
// false and fell through to the caller's unrecognized-option branch, which told
// the reader an option that exists does not. A --protect-named-key whose value
// was not §34.5.10's <owner>:<name>=<key> was answered the same way, with
// nothing saying which part of the value was missing. Each option now answers
// true for such a value, having reported it and set
// ProtectCliOptions::rejected_argument, and a case asserting one half alone
// would pass against a parser carrying only half of that.
//
// Each case over a refused value is paired with a case giving the same option a
// value the option accepts, so a parser that refused every value would fail the
// pair.

#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <vector>

#include "preprocessor/protect_cli.h"

using namespace delta;

namespace {

// Reads a whole command line, as the binary's own loop does, and hands back
// what the protect options took off it. The loop is what a caller runs, so a
// case naming one option states what the run was asked for rather than what one
// call returned.
ProtectCliOptions Parsed(std::initializer_list<const char*> args) {
  std::vector<const char*> argv(args);
  ProtectCliOptions opts;
  for (int i = 0; i < static_cast<int>(argv.size()); ++i) {
    TryParseProtectArg(argv[static_cast<size_t>(i)], i,
                       static_cast<int>(argv.size()), argv.data(), opts);
  }
  return opts;
}

// Both halves of what one call to TryParseProtectArg answers: whether the
// argument was one of these options, and what the call left in the options it
// was given.
struct ProtectArgParse {
  bool recognized = false;
  ProtectCliOptions opts;
};

// Reads the first argument of `args` with the rest of `args` standing after it
// on the command line, and hands back both halves. A case over an option
// written last passes that option alone, so `argc` stops where the option does
// and there is no value after it to read.
ProtectArgParse ParsedArg(std::initializer_list<const char*> args) {
  std::vector<const char*> argv(args);
  ProtectArgParse parse;
  int i = 0;
  parse.recognized = TryParseProtectArg(
      argv[0], i, static_cast<int>(argv.size()), argv.data(), parse.opts);
  return parse;
}

// §34.3.1 gives a protected envelope two modes of processing, and an encrypting
// tool reads the encryption envelopes an author wrote and leaves a decryption
// envelope in the place of each. Nothing asked deltahdl for that mode before
// this option existed, so §34.3.1's encrypting half was reachable from no
// invocation.
TEST(ProtectCliParsing, EncryptOptionIsRecorded) {
  EXPECT_TRUE(Parsed({"--encrypt"}).encrypt);
}

// The mode is not the default, so a command line that does not ask for it does
// not get it. Without this a run that only supplied a key would encrypt.
TEST(ProtectCliParsing, EncryptIsOffWhenUnasked) {
  EXPECT_FALSE(Parsed({"--protect-key", "acme-key"}).encrypt);
}

// §34.5.10's first arrangement: one key encrypts every region, whoever the
// region names.
TEST(ProtectCliParsing, ExchangeKeyIsRecorded) {
  EXPECT_EQ(Parsed({"--protect-key", "acme-key"}).exchange_key, "acme-key");
}

// §34.5.10's other arrangement: a key is selected by whose it is and which of
// theirs it is, so a text naming several entities has each region encrypted
// under a key of the entity that region names.
TEST(ProtectCliParsing, NamedKeyIsRecordedUnderItsOwnerAndName) {
  auto opts = Parsed({"--protect-named-key", "acme:rsa-2048=acme-key"});
  EXPECT_EQ(opts.keys.KeyFor("acme", "rsa-2048"), "acme-key");
}

// The two arrangements are not alternatives to one another, so supplying one
// does not empty the other.
TEST(ProtectCliParsing, ANamedKeyLeavesTheExchangeKeyAlone) {
  auto opts = Parsed({"--protect-key", "acme-key", "--protect-named-key",
                      "widget:rsa-2048=widget-key"});
  EXPECT_EQ(opts.exchange_key, "acme-key");
}

// --protect-key written last has no value to take, and the option says so
// itself rather than handing the argument back. Answering false would send the
// argument to the caller's unrecognized-option branch, which reports an option
// that exists as one that does not; that is the defect issue #3427 names.
TEST(ProtectCliParsing, ExchangeKeyWithNoValueIsRefusedRatherThanUnrecognized) {
  auto parse = ParsedArg({"--protect-key"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

// The same for the named form, whose value carries three things rather than
// one.
TEST(ProtectCliParsing, NamedKeyWithNoValueIsRefusedRatherThanUnrecognized) {
  auto parse = ParsedArg({"--protect-named-key"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

// §34.5.10 selects a key by the entity that owns it and the name it was given,
// so a value with no ':' names no entity. The option took the value and refused
// it, which is why the case asserts the refusal rather than a fall-through.
TEST(ProtectCliParsing, NamedKeyWithNoColonIsRefused) {
  auto parse = ParsedArg({"--protect-named-key", "rsa-2048=acme-key"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

// The other separator of <owner>:<name>=<key>, which AddNamedKey
// (preprocessor/protect_cli.cpp) searches for only after the ':' it found. A
// value naming an entity and a name but no key is refused too.
TEST(ProtectCliParsing, NamedKeyWithNoEqualsIsRefused) {
  auto parse = ParsedArg({"--protect-named-key", "acme:rsa-2048"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

// Both separators are written and the entity's name is still not there.
// AddNamedKey (preprocessor/protect_cli.cpp) checks the three parts for
// emptiness after it has found both separators, so a case over a missing
// separator says nothing about this one.
TEST(ProtectCliParsing, NamedKeyWithAnEmptyOwnerIsRefused) {
  auto parse = ParsedArg({"--protect-named-key", ":rsa-2048=acme-key"});
  EXPECT_TRUE(parse.recognized);
  EXPECT_TRUE(parse.opts.rejected_argument);
}

// A named key needs all three of owner, name and key, since §34.5.10 selects on
// the first two. A value missing the separator names no owner, so it is refused
// rather than stored under an empty one.
TEST(ProtectCliParsing, NamedKeyWithoutAnOwnerIsRefused) {
  auto opts = Parsed({"--protect-named-key", "rsa-2048=acme-key"});
  EXPECT_FALSE(opts.keys.KnowsOwner("rsa-2048"));
}

// The value --protect-key accepts, which is what keeps the refusals above from
// passing against a parser that refused every value.
TEST(ProtectCliParsing, ExchangeKeyWithAValueSetsNoRejectedArgument) {
  auto parse = ParsedArg({"--protect-key", "acme-key"});
  EXPECT_EQ(parse.opts.exchange_key, "acme-key");
  EXPECT_FALSE(parse.opts.rejected_argument);
}

// The value --protect-named-key accepts, read back through ProtectKeyList
// (preprocessor/protect_keywords.h) under the two names §34.5.10 selects on.
TEST(ProtectCliParsing, NamedKeyWithAWellFormedValueSetsNoRejectedArgument) {
  auto parse = ParsedArg({"--protect-named-key", "acme:rsa-2048=acme-key"});
  EXPECT_EQ(parse.opts.keys.KeyFor("acme", "rsa-2048"), "acme-key");
  EXPECT_FALSE(parse.opts.rejected_argument);
}

// --encrypt takes no value, so nothing about it can be refused.
// ProtectCliOptions::rejected_argument records a value the option would not
// take, and an option that reads no value never sets it.
TEST(ProtectCliParsing, EncryptSetsNoRejectedArgument) {
  auto parse = ParsedArg({"--encrypt"});
  EXPECT_TRUE(parse.opts.encrypt);
  EXPECT_FALSE(parse.opts.rejected_argument);
}

// An argument that is none of these is left for the option groups beside this
// one, which is what keeps the binary's other options working.
TEST(ProtectCliParsing, AnUnrelatedArgumentIsNotConsumed) {
  const char* argv[] = {"--lint-only"};
  int i = 0;
  ProtectCliOptions opts;
  EXPECT_FALSE(TryParseProtectArg(argv[0], i, 1, argv, opts));
}

}  // namespace
