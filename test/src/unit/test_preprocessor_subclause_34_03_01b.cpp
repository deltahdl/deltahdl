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

// An option whose value is missing is not consumed, so the caller reports it as
// an unknown option rather than reading past the end of argv. This is the case
// #3115 names as the one the option table has to reject.
TEST(ProtectCliParsing, ExchangeKeyWithNoValueIsNotConsumed) {
  const char* argv[] = {"--protect-key"};
  int i = 0;
  ProtectCliOptions opts;
  EXPECT_FALSE(TryParseProtectArg(argv[0], i, 1, argv, opts));
}

// The same for the named form, whose value carries three things rather than
// one.
TEST(ProtectCliParsing, NamedKeyWithNoValueIsNotConsumed) {
  const char* argv[] = {"--protect-named-key"};
  int i = 0;
  ProtectCliOptions opts;
  EXPECT_FALSE(TryParseProtectArg(argv[0], i, 1, argv, opts));
}

// A named key needs all three of owner, name and key, since §34.5.10 selects on
// the first two. A value missing the separator names no owner, so it is refused
// rather than stored under an empty one.
TEST(ProtectCliParsing, NamedKeyWithoutAnOwnerIsRefused) {
  auto opts = Parsed({"--protect-named-key", "rsa-2048=acme-key"});
  EXPECT_FALSE(opts.keys.KnowsOwner("rsa-2048"));
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
