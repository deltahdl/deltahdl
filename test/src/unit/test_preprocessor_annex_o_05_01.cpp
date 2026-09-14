#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The recipient of the envelope: its owner identity, the name of the key of
// its that the sender holds, and the key, standing for the public key the
// sender encrypts under and the private key the recipient opens with.
constexpr std::string_view kRecipient = "lyra-eda";
constexpr std::string_view kRecipientsKeyName = "lyra-2026";
constexpr std::string_view kRecipientsKey = "lyra-envelope-key";

// The name of the symmetric key the design is under, which nobody's run
// holds, and the design.
constexpr std::string_view kProvidersKeyName = "core-2026";
constexpr std::string_view kDesign = "  initial result = 42;\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// The keys a run holds: the recipient's under its owner and name, or none.
ProtectKeyList RecipientsKeys() {
  ProtectKeyList keys;
  keys.Add({std::string(kRecipient), std::string(kRecipientsKeyName),
            std::string(kRecipientsKey)});
  return keys;
}

// One expression of the input, its value quoted.
std::string Pragma(std::string_view keyword, std::string_view value) {
  std::string line = "`pragma protect ";
  line.append(keyword).append("=\"").append(value).append("\"\n");
  return line;
}

// The input's expected pragmas, with `key_method` as the scheme named for
// the recipient's key, ahead of the region they designate keys for.
std::string ExpectedInput(std::string_view key_method) {
  std::string src = Pragma("key_keyowner", kRecipient);
  src += Pragma("key_method", key_method);
  src += Pragma("key_keyname", kRecipientsKeyName);
  src += Pragma("data_keyname", kProvidersKeyName);
  src += "`pragma protect begin\n";
  src.append(kDesign);
  src += "`pragma protect end\n";
  return src;
}

// The sender's run over `src`, holding the recipient's key, and what it
// reported.
struct Sending {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string envelope;

  explicit Sending(const std::string& src) {
    envelope = EncryptEnvelopes(src, "", RecipientsKeys(), &diag,
                                mgr.AddFile("<sender>", src));
  }
};

// Whether a run of `envelope` holding `keys` gets the design out of it.
bool Opens(const std::string& envelope, const ProtectKeyList& keys) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = keys;
  Preprocessor pp(mgr, diag, config);
  return Holds(pp.Preprocess(mgr.AddFile("<recipient>", envelope)),
               "initial result = 42;");
}

// §O.5.1: the input expects key_keyowner, key_method, key_keyname and
// data_keyname with begin and end around the regions, and may include the
// eight pragmas §O.3.1's input may, data_keyowner being required to be the
// owner of the key name provided. Every name is a keyword §34.4 tabulates.
TEST(DigitalEnvelopeInput, TheExpectedAndOptionalPragmasAreTheAnnexs) {
  auto expected = PragmasExpectedByDigitalEnvelopeInput();
  ASSERT_EQ(expected.size(), 6u);
  EXPECT_EQ(expected[0], "key_keyowner");
  EXPECT_EQ(expected[1], "key_method");
  EXPECT_EQ(expected[2], "key_keyname");
  EXPECT_EQ(expected[3], "data_keyname");
  EXPECT_EQ(expected[4], "begin");
  EXPECT_EQ(expected[5], "end");
  auto optional = PragmasOptionalInDigitalEnvelopeInput();
  ASSERT_EQ(optional.size(), 8u);
  EXPECT_EQ(optional[2], "data_keyowner");
  EXPECT_TRUE(DataKeyownerShallBeTheOwnerOfTheKeyNameProvided());
  for (std::string_view name : expected) {
    EXPECT_TRUE(IsProtectPragmaKeyword(name)) << name;
    for (std::string_view other : optional) EXPECT_NE(name, other);
  }
  for (std::string_view name : optional) {
    EXPECT_TRUE(IsProtectPragmaKeyword(name)) << name;
  }
}

// §O.5.1 against the flow: the expected pragmas, key_method naming
// §34.5.11's required des-cbc, form an envelope without a report -- the
// design in no clear line, one key_block for the recipient sealed under the
// scheme the envelope states -- that the recipient's run opens with its own
// key and a run holding no key does not.
TEST(DigitalEnvelopeInput, TheExpectedPragmasFormAnEnvelopeTheRecipientOpens) {
  Sending run(ExpectedInput("des-cbc"));
  EXPECT_FALSE(run.diag.HasErrors()) << run.envelope;
  EXPECT_TRUE(Holds(run.envelope, "`pragma protect key_block\n"));
  EXPECT_TRUE(Holds(run.envelope, "`pragma protect key_method=\"des-cbc\"\n"));
  EXPECT_FALSE(Holds(run.envelope, "result = 42"));
  EXPECT_TRUE(Opens(run.envelope, RecipientsKeys()));
  EXPECT_FALSE(Opens(run.envelope, ProtectKeyList()));
}

// §O.5.1 as this tool has it: the scheme key_method names is what the key
// block is sealed under, and this tool seals one under des-cbc or its own
// cipher and under nothing else, so an input naming rsa for the recipient's
// key draws §34.5.24.2's report for an algorithm the implementation does
// not provide, one Table 34-3 does not require of every implementation.
TEST(DigitalEnvelopeInput, AKeyMethodThisToolDoesNotProvideIsReported) {
  auto methods = KeyMethodsThisToolSealsAKeyBlockUnder();
  ASSERT_EQ(methods.size(), 2u);
  EXPECT_EQ(methods[0], "des-cbc");
  EXPECT_EQ(methods[1], "x-deltahdl-stream");
  std::string src = ExpectedInput("rsa");
  Sending run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "protect pragma key_method asks for an encryption "
                            "algorithm this implementation does not provide: "
                            "rsa, which IEEE 1800-2023 Table 34-3 does not "
                            "require of every implementation",
                            LineHolding(src, "key_method"), "34.5.24.2"));
}

// §O.5.1 against the flow: the eight optional pragmas may be included, the
// key owner among them being the owner of the name provided, and an input
// including all of them beside the expected ones is accepted without a
// report and forms an envelope the recipient opens the same way.
TEST(DigitalEnvelopeInput, TheOptionalPragmasMayBeIncluded) {
  std::string src = Pragma("author", "Core Author");
  src += Pragma("author_info", "revision 5");
  src += Pragma("data_keyowner", "core-ip");
  src += Pragma("data_method", "des-cbc");
  src += "`pragma protect encoding=(enctype=\"base64\")\n";
  src += "`pragma protect digest_block\n";
  src +=
      "`pragma protect decrypt_license=(library=\"lic.so\", "
      "entry=\"acquire\", feature=\"open\")\n";
  src +=
      "`pragma protect runtime_license=(library=\"lic.so\", "
      "entry=\"acquire\", feature=\"run\")\n";
  src += ExpectedInput("des-cbc");
  Sending run(src);
  EXPECT_FALSE(run.diag.HasErrors()) << run.envelope;
  EXPECT_TRUE(Holds(run.envelope, "author=\"Core Author\""));
  EXPECT_FALSE(Holds(run.envelope, "result = 42"));
  EXPECT_TRUE(Opens(run.envelope, RecipientsKeys()));
}

}  // namespace
