#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "fixture_preprocessor.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

// Every version byte the preprocessor planted in `out`, in order. A source
// with no `begin_keywords/`end_keywords directive at all yields an empty list.
// A marker occupies a line of its own — marker, version byte, newline — so
// only a marker at the start of a line opens one; the byte that follows may
// happen to equal the marker itself, which is how 1364-2001 encodes.
std::vector<KeywordVersion> MarkedVersions(const std::string& out) {
  std::vector<KeywordVersion> versions;
  for (size_t pos = 0; pos + 1 < out.size(); ++pos) {
    if (out[pos] != kKeywordMarker) continue;
    if (pos != 0 && out[pos - 1] != '\n') continue;
    versions.push_back(
        static_cast<KeywordVersion>(static_cast<uint8_t>(out[pos + 1])));
    ++pos;  // the version byte is data, never the start of another marker
  }
  return versions;
}

// The offset just past the last version marker in `out`.
size_t EndOfLastMarker(const std::string& out) {
  size_t last = 0;
  for (size_t pos = 0; pos + 1 < out.size(); ++pos) {
    if (out[pos] != kKeywordMarker) continue;
    if (pos != 0 && out[pos - 1] != '\n') continue;
    last = pos + 2;
    ++pos;
  }
  return last;
}

// The module of the §22.14.1 examples, written out with the port list and body
// the LRM elides. `logic` names the 64-bit variable, which is what makes the
// same text legal under one reserved word list and illegal under another.
constexpr const char* kM2Module =
    "module m2 (input wire clk, output wire q);\n"
    "  reg [63:0] logic;\n"
    "endmodule\n";

// The interface of the later §22.14.1 examples, likewise with the elided port
// list and body filled in.
constexpr const char* kInterface =
    "interface if1 (input wire clk);\n"
    "  wire [7:0] data;\n"
    "endinterface\n";

std::string Guarded(const std::string& specifier, const std::string& body) {
  return "`begin_keywords \"" + specifier + "\"\n" + body + "`end_keywords\n";
}

// §22.14.1's first example: a module written with no `begin_keywords directive
// governing it. Nothing selects a reserved word list, so the preprocessor
// plants no version marker and the downstream stages fall back on the
// implementation's default set.
TEST(KeywordVersionExamplePreproc, ModuleWithNoDirectiveIsLeftUnmarked) {
  PreprocFixture f;
  auto out = Preprocess("module m1;\n  reg [63:0] v;\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(MarkedVersions(out).empty());
  EXPECT_NE(out.find("module m1;"), std::string::npos);
}

// The same claim reached from the other syntactic position: a module that
// simply follows a closed pair has no `begin_keywords in effect either. The
// closing directive restores the default list, so the marker standing between
// the two modules names this implementation's default rather than the
// specifier the closed region had selected.
TEST(KeywordVersionExamplePreproc, ModuleAfterAClosedPairIsBackToTheDefault) {
  PreprocFixture f;
  auto out = Preprocess(Guarded("1364-2001", kM2Module) +
                            "module m1;\n  reg [63:0] v;\nendmodule\n",
                        f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto versions = MarkedVersions(out);
  ASSERT_EQ(versions.size(), 2u);
  EXPECT_EQ(versions[0], KeywordVersion::kVer13642001);
  EXPECT_EQ(versions[1], KeywordVersion::kVer18002023);

  // m1's text arrives after the closing marker, i.e. outside the region.
  auto module_pos = out.find("module m1;");
  ASSERT_NE(module_pos, std::string::npos);
  EXPECT_LT(EndOfLastMarker(out), module_pos);
}

// The first example turns on the directive being absent *ahead of* the module
// definition, so a directive that appears only later must not reach back over
// it. The marker lands where the directive stood rather than at the head of
// the output, leaving the earlier module governed by the default list.
TEST(KeywordVersionExamplePreproc, ModuleAheadOfTheFirstPairIsUnmarked) {
  PreprocFixture f;
  auto out = Preprocess("module m1;\n  reg [63:0] v;\nendmodule\n" +
                            Guarded("1364-2001", kM2Module),
                        f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto versions = MarkedVersions(out);
  ASSERT_EQ(versions.size(), 2u);
  EXPECT_EQ(versions[0], KeywordVersion::kVer13642001);

  auto module_pos = out.find("module m1;");
  ASSERT_NE(module_pos, std::string::npos);
  EXPECT_LT(module_pos, out.find(kKeywordMarker));
}

// The specifiers §22.14.1 names over the module its examples share: the
// "1364-2001" of the second example, the "1364-1995" and "1364-2005" the same
// example says would serve just as well, and the "1800-2005" of the third —
// the one spelling the LRM calls an error. Each reaches the marker as itself,
// and the enclosed text is handed on untouched in every case, including the
// erroring one: at this stage the declaration is just characters, and which of
// them are reserved words is settled downstream.
TEST(KeywordVersionExamplePreproc, EachModuleExampleSpecifierReachesTheMarker) {
  const std::pair<const char*, KeywordVersion> kCases[] = {
      {"1364-2001", KeywordVersion::kVer13642001},
      {"1364-1995", KeywordVersion::kVer13641995},
      {"1364-2005", KeywordVersion::kVer13642005},
      {"1800-2005", KeywordVersion::kVer18002005},
  };
  for (const auto& [specifier, expected] : kCases) {
    PreprocFixture f;
    auto out = Preprocess(Guarded(specifier, kM2Module), f);
    EXPECT_FALSE(f.diag.HasErrors()) << specifier;

    auto versions = MarkedVersions(out);
    ASSERT_EQ(versions.size(), 2u) << specifier;
    EXPECT_EQ(versions[0], expected) << specifier;

    EXPECT_NE(out.find("reg [63:0] logic;"), std::string::npos) << specifier;
    // The directive lines themselves are consumed, not passed through.
    EXPECT_EQ(out.find("begin_keywords"), std::string::npos) << specifier;
  }
}

// §22.14.1's last two examples wrap an interface rather than a module, which
// is the other kind of design element a region has to carry here. Both the
// "1800-2005" spelling the LRM accepts and the "1364-2005" one it says errors
// are marked and passed on the same way, so what separates the two examples is
// the marker byte alone — the words that delimit the interface are classified
// further down the pipeline.
TEST(KeywordVersionExamplePreproc,
     EachInterfaceExampleSpecifierReachesTheMarker) {
  const std::pair<const char*, KeywordVersion> kCases[] = {
      {"1800-2005", KeywordVersion::kVer18002005},
      {"1364-2005", KeywordVersion::kVer13642005},
  };
  for (const auto& [specifier, expected] : kCases) {
    PreprocFixture f;
    auto out = Preprocess(Guarded(specifier, kInterface), f);
    EXPECT_FALSE(f.diag.HasErrors()) << specifier;

    auto versions = MarkedVersions(out);
    ASSERT_EQ(versions.size(), 2u) << specifier;
    EXPECT_EQ(versions[0], expected) << specifier;

    EXPECT_NE(out.find("interface if1"), std::string::npos) << specifier;
    EXPECT_NE(out.find("endinterface"), std::string::npos) << specifier;
  }
}

}  // namespace
